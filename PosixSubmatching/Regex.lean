universe u

inductive Regex (α :  Type u) : Type u where
  | emptyset : Regex α
  | epsilon : Regex α
  | char : α → Regex α
  | plus : Regex α → Regex α → Regex α
  | mul : Regex α → Regex α → Regex α
  | star : Regex α → Regex α
  | group : String → List α → Regex α → Regex α
  deriving Repr

namespace Regex

variable {α : Type u}

@[simp]
def nullable : Regex α → Bool
  | emptyset => false
  | epsilon => true
  | char _ => false
  | plus r₁ r₂ => r₁.nullable || r₂.nullable
  | mul r₁ r₂ => r₁.nullable && r₂.nullable
  | star _ => true
  | group _ _ r => r.nullable

def markEmpty : Regex α → Regex α
  | emptyset => emptyset
  | char _ => emptyset
  | epsilon => epsilon
  | plus r₁ r₂ => plus r₁.markEmpty r₂.markEmpty
  | mul r₁ r₂ => mul r₁.markEmpty r₂.markEmpty
  | star r => star r.markEmpty
  | group n s r => group n s r.markEmpty

variable [DecidableEq α]

@[simp]
def deriv : Regex α → α → Regex α
  | emptyset, _ => emptyset
  | epsilon, _ => emptyset
  | char d, c => if c = d then epsilon else emptyset
  | plus r₁ r₂, c => (r₁.deriv c).plus (r₂.deriv c)
  | mul r₁ r₂, c =>
    if r₁.nullable
      then ((r₁.deriv c).mul r₂).plus (r₁.markEmpty.mul (r₂.deriv c))
      else (r₁.deriv c).mul r₂
  | star r, c => (r.deriv c).mul r.star
  | group n s r, c => group n (c :: s) (r.deriv c)

@[simp]
def derivs : Regex α → List α → Regex α
  | r, [] => r
  | r, c::s => (r.deriv c).derivs s

def extract : (r : Regex α) → r.nullable → List (String × List α)
  | epsilon, _ => []
  | plus r₁ r₂, hr =>
    if hr₁ : r₁.nullable
      then extract r₁ hr₁
      else by
        simp at hr
        exact extract r₂ (Or.resolve_left hr hr₁)
  | mul r₁ r₂, hr => by
    simp at hr
    exact extract r₁ hr.left ++ extract r₂ hr.right
  | star r, _ => []
  | group n s r, hr => ⟨n, s.reverse⟩ :: extract r hr

def captures : Regex α → List α → List (String × List α)
  | r, s =>
    let r' := r.derivs s
    if h : r'.nullable then extract r' h else []
