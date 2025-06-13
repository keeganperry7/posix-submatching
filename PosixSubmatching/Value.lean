import PosixSubmatching.Regex
import Mathlib.Tactic.SplitIfs

universe u

inductive Value (α : Type u)
  | empty : Value α
  | char : α → Value α
  | left : Value α → Value α
  | right : Value α → Value α
  | seq : Value α → Value α → Value α
  | stars : List (Value α) → Value α
  deriving Repr

variable {α : Type u}

@[simp]
def Value.flat : Value α → List α
  | empty => []
  | char c => [c]
  | left v => v.flat
  | right v => v.flat
  | seq v₁ v₂ => v₁.flat ++ v₂.flat
  | stars [] => []
  | stars (v::vs) => v.flat ++ (stars vs).flat

open Value
open Regex

inductive Inhab : Value α → Regex α → Prop
  | empty : Inhab empty epsilon
  | char (c : α) : Inhab (char c) (char c)
  | left {v₁ : Value α} {r₁ r₂ : Regex α} :
    Inhab v₁ r₁ →
    Inhab (left v₁) (plus r₁ r₂)
  | right {v₂ : Value α} {r₁ r₂ : Regex α} :
    Inhab v₂ r₂ →
    Inhab (right v₂) (plus r₁ r₂)
  | seq {v₁ v₂ : Value α} {r₁ r₂ : Regex α} :
    Inhab v₁ r₁ →
    Inhab v₂ r₂ →
    Inhab (seq v₁ v₂) (mul r₁ r₂)
  | star_nil {r : Regex α} :
    Inhab (stars []) (star r)
  | stars {v : Value α} {vs : List (Value α)} {r : Regex α} :
    -- v.flat ≠ [] →
    Inhab v r →
    Inhab (stars vs) (star r) →
    Inhab (stars (v::vs)) (star r)
  | group {v : Value α} {n : String} {s : List α} {r : Regex α} :
    Inhab v r →
    Inhab v (group n s r)

@[simp]
theorem inhab_zero {v : Value α} :
  ¬Inhab v emptyset := by
  intro h
  cases h

theorem inhab_left {v₁ : Value α} {r₁ r₂ : Regex α} :
  Inhab (left v₁) (plus r₁ r₂) → Inhab v₁ r₁ := by
  intro h
  cases h with
  | left h =>
    exact h

theorem inhab_right {v₂ : Value α} {r₁ r₂ : Regex α} :
  Inhab (right v₂) (plus r₁ r₂) → Inhab v₂ r₂ := by
  intro h
  cases h with
  | right h =>
    exact h

theorem inhab_seq {v₁ v₂ : Value α} {r₁ r₂ : Regex α} :
  Inhab (seq v₁ v₂) (mul r₁ r₂) → Inhab v₁ r₁ ∧ Inhab v₂ r₂ := by
  intro h
  cases h with
  | seq h₁ h₂ => exact ⟨h₁, h₂⟩

theorem inhab_seq_fst {v₁ v₂ : Value α} {r₁ r₂ : Regex α} :
  Inhab (seq v₁ v₂) (mul r₁ r₂) → Inhab v₁ r₁ := by
  intro h
  cases h with
  | seq h₁ _ => exact h₁

theorem inhab_seq_snd {v₁ v₂ : Value α} {r₁ r₂ : Regex α} :
  Inhab (seq v₁ v₂) (mul r₁ r₂) → Inhab v₂ r₂ := by
  intro h
  cases h with
  | seq _ h₂ => exact h₂

theorem inhab_stars_head {v : Value α} {vs : List (Value α)} {r : Regex α} :
  Inhab (stars (v::vs)) (star r) → Inhab v r := by
  intro h
  cases h with
  | stars h₁ _ => exact h₁

theorem inhab_stars_tail {v : Value α} {vs : List (Value α)} {r : Regex α} :
  Inhab (stars (v::vs)) (star r) → Inhab (stars vs) r.star := by
  intro h
  cases h with
  | stars _ h₂ => exact h₂

theorem inhab_group {v : Value α} {n : String} {s : List α} {r : Regex α} :
  Inhab v (group n s r) → Inhab v r := by
  intro h
  cases h with
  | group h => exact h

theorem Inhab_not_nullable {r : Regex α} {v : Value α} (hn : ¬r.nullable) (hv : v.flat = []) :
  ¬Inhab v r := by
  intro h
  induction r generalizing v with
  | emptyset => nomatch h
  | epsilon => simp at hn
  | char =>
    cases h with
    | char => simp at hv
  | plus r₁ r₂ ih₁ ih₂ =>
    simp at hn
    cases h with
    | left h =>
      apply ih₁
      simp [hn]
      simp at hv
      exact hv
      exact h
    | right h =>
      apply ih₂
      simp [hn]
      simp at hv
      exact hv
      exact h
  | mul r₁ r₂ ih₁ ih₂ =>
    cases h with
    | seq h₁ h₂ =>
      simp at hv
      simp at hn
      apply ih₁
      intro hn₁
      apply ih₂
      simp [hn hn₁]
      exact hv.right
      exact h₂
      exact hv.left
      exact h₁
  | star r => simp at hn
  | group n s r ih =>
    cases h with
    | group h => exact ih hn hv h

def Regex.mkeps (r : Regex α) (hn : r.nullable) : (Σ' v : Value α, Inhab v r) :=
  match r with
  | epsilon => ⟨Value.empty, Inhab.empty⟩
  | mul r₁ r₂ => by
    simp [nullable] at hn
    have ⟨v₁, h₁⟩ := mkeps r₁ hn.left
    have ⟨v₂, h₂⟩ := mkeps r₂ hn.right
    exact ⟨Value.seq v₁ v₂, Inhab.seq h₁ h₂⟩
  | plus r₁ r₂ => by
    if hn₁ : r₁.nullable
      then
        have ⟨v₁, h₁⟩ := mkeps r₁ hn₁
        exact ⟨Value.left v₁, Inhab.left h₁⟩
      else
        simp [nullable] at hn
        have ⟨v₂, h₂⟩ := mkeps r₂ (Or.resolve_left hn hn₁)
        exact ⟨Value.right v₂, Inhab.right h₂⟩
  | .star r => ⟨Value.stars [], Inhab.star_nil⟩
  | group n s r =>
    have ⟨v, h⟩ := mkeps r hn
    ⟨v, Inhab.group h⟩

variable [DecidableEq α]

def inj : (r : Regex α) → (c : α) → (Σ' v : Value α, Inhab v (r.deriv c)) → (Σ' v : Value α, Inhab v r)
  | .char d, c, ⟨v, h⟩ => ⟨Value.char d, Inhab.char d⟩
  | .plus r₁ r₂, c, ⟨Value.left v₁, h₁⟩ =>
    have ⟨v₁, h₁⟩ := inj r₁ c ⟨v₁, inhab_left h₁⟩
    ⟨v₁.left, h₁.left⟩
  | .plus r₁ r₂, c, ⟨Value.right v₂, h₂⟩ =>
    have ⟨v₂, h₂⟩ := inj r₂ c ⟨v₂, inhab_right h₂⟩
    ⟨v₂.right, h₂.right⟩
  | .mul r₁ r₂, c, ⟨v, h⟩ => by
    rw [Regex.deriv] at h
    split_ifs at h with hn
    · match v with
      | Value.left (Value.seq v₁ v₂) =>
        have ⟨v₁, h₁⟩ := inj r₁ c ⟨v₁, inhab_seq_fst (inhab_left h)⟩
        exact ⟨v₁.seq v₂, h₁.seq (inhab_seq_snd (inhab_left h))⟩
      | Value.right (Value.seq v₁ v₂) =>
        have ⟨v₂, h₂⟩ := inj r₂ c ⟨v₂, inhab_seq_snd (inhab_right h)⟩
        exact ⟨v₁.seq v₂, (inhab_seq_fst (inhab_right h)).seq h₂⟩
    · match v with
      | Value.seq v₁ v₂ =>
        have ⟨v₁, h₁⟩ := inj r₁ c ⟨v₁, inhab_seq_fst h⟩
        exact ⟨v₁.seq v₂, h₁.seq (inhab_seq_snd h)⟩
  | .star r, c, ⟨Value.seq v (Value.stars vs), h⟩ =>
    have ⟨v, hv⟩ := inj r c ⟨v, inhab_seq_fst h⟩
    ⟨Value.stars (v :: vs), Inhab.stars hv (inhab_seq_snd h)⟩
  | .group n s r, c, ⟨v, h⟩ =>
    have ⟨v, h⟩ := inj r c ⟨v, inhab_group h⟩
    ⟨v, Inhab.group h⟩

def injs : (r : Regex α) → (s : List α) → (Σ' v : Value α, Inhab v (r.derivs s)) → (Σ' v' : Value α, Inhab v' r)
  | _, [], h => h
  | r, c::s, h => inj r c (injs (r.deriv c) s h)

def Regex.extract' : (r : Regex α) → (Σ' v : Value α, Inhab v r) → List (String × List α)
  | epsilon, _ => []
  | char _, _ => []
  | plus r₁ r₂, ⟨Value.left v₁, h₁⟩ =>
    r₁.extract' ⟨v₁, inhab_left h₁⟩
  | plus r₁ r₂, ⟨Value.right v₂, h₂⟩ =>
    r₂.extract' ⟨v₂, inhab_right h₂⟩
  | mul r₁ r₂, ⟨Value.seq v₁ v₂, h⟩ =>
    r₁.extract' ⟨v₁, inhab_seq_fst h⟩ ++ r₂.extract' ⟨v₂, inhab_seq_snd h⟩
  | star _, ⟨Value.stars [], _⟩ => []
  | star r, ⟨Value.stars (v::vs), h⟩ =>
    r.extract' ⟨v, inhab_stars_head h⟩ ++ (star r).extract' ⟨Value.stars vs, inhab_stars_tail h⟩
  | group n _ r, ⟨v, h⟩ => (n, v.flat) :: r.extract' ⟨v, inhab_group h⟩

def Regex.captures' : Regex α → List α → List (String × List α)
  | r, s =>
    let r' := r.derivs s
    if h : r'.nullable
      then r.extract' (injs r s (r'.mkeps h))
      else []

def Regex.parse : Regex α → List α → Option (Value α)
  | r, s =>
    let r' := r.derivs s
    if h : r'.nullable
      then some (injs r s (r'.mkeps h)).fst
      else none
