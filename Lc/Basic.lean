import Lean
import Qq

inductive Term where
  | var (name : String)
  | lam (name : String) (body : Term)
  | app (f x : Term)
  | letIn (name : String) (defs rest : Term)
  deriving Repr

-- https://arxiv.org/pdf/1805.08059.pdf
-- http://strictlypositive.org
-- http://adam.chlipala.net/papers/PhoasICFP08/PhoasICFP08.pdf
-- https://lean-lang.org/lean4/doc/examples/phoas.lean.html
unsafe inductive Value where
  | var (name : String)
  | lam (name : String) (f : Value -> Option Value)
  | app (f x : Value)

unsafe abbrev Env := List (String × Value)

mutual
  unsafe def eval (env : Env) : Term -> Option Value
    | .var name => env.lookup name
    | .letIn name defs rest => do
        let defs <- eval env defs
        eval ((name, defs) :: env) rest
    | .lam x body => .lam x <$> fun v => eval ((x, v) :: env) body
    | .app f x => do doApp (<- eval env f) (<- eval env x)

  unsafe def doApp (f x : Value) : Option Value :=
    match f with
    | .lam _ f => f x
    | f => return .app f x
end

unsafe def fresh (names : List String) (name : String) : String :=
  if names.elem name
    then fresh names (name ++ "'")
    else name

unsafe def quote (used : List String) : Value -> Option Term
  | .var name => return .var name
  | .app f x => return .app (<- quote used f) (<- quote used x)
  | .lam x body =>
      let x := fresh used x
      do Term.lam x (<- quote (x :: used) (<- body (.var x)))

unsafe def normalize (env : Env) : Term -> Option Term :=
  (quote (Prod.fst <$> env) =<< ·) ∘ eval env

#eval normalize [] (.lam "x" $ .var "x")

declare_syntax_cat lc
syntax ident : lc
syntax "let " ident " := " lc " in " lc : lc
syntax "fun " ident " => " lc : lc
syntax lc (ppSpace colGt lc)+ : lc
syntax "( " lc " )" : lc

open Lean Meta Elab Term Qq

unsafe def parseTerm : TSyntax `lc -> _root_.Term
  | `(lc| $x:ident) => .var s!"{x}"
  | `(lc| let $x:ident := $term:lc in $rest:lc) =>
      .letIn s!"{x}" (parseTerm term) (parseTerm rest)
  | `(lc| fun $x => $body) =>
      .lam s!"{x}" $ parseTerm body
  | `(lc| $f:lc $xs:lc*) =>
      (xs.map parseTerm).foldl
        (fun acc x => .app acc x)
        (parseTerm f)
  | `(lc| ( $x:lc )) => parseTerm x
  | _ => .var "___ERROR___parseTerm"

syntax (name := lc_term) "LC[" lc "]" : term

def toTerm : _root_.Term -> TermElabM Expr
  | .var name => return q(_root_.Term.var $name)
  | .lam x body => do
      let f : Expr := q(_root_.Term.lam $x)
      return Expr.app f (<- toTerm body)
  | .app f x => do
      return Expr.app (<- toTerm f) (<- toTerm x)
  | .letIn name defs rest => do
      return mkAppN q(Expr.app)
        #[q($name)
         , <- toTerm defs
         , <- toTerm rest
         ]

@[term_elab lc_term]
unsafe def evalLcTerm : TermElab := fun stx _ =>
  match stx with
  | `(term| LC[ $t:lc ]) => do
      -- logInfo (reprStr (parseTerm t))
      match normalize [] $ parseTerm t with
      | .none => return q("___ERROR___evalLcTerm")
      | .some t => toTerm t
  | _ => throwUnsupportedSyntax

#eval LC[ fun x => x ]
#eval LC[
  let id := fun x => x in
  (id id)
]
#eval LC[
  let id := fun x => x in
  (id id) id (id id)
]
#eval LC[
  let id := fun x => x in
  id id id id
]

-- https://en.wikipedia.org/wiki/Church_encoding
-- Church numerals
