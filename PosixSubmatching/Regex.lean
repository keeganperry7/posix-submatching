import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.ApplyAt

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

inductive Matches : List α → Regex α → Prop
  | epsilon : Matches [] epsilon
  | char {c : α} : Matches [c] (char c)
  | plus_left {s : List α} {r₁ r₂ : Regex α} :
    Matches s r₁ →
    Matches s (r₁.plus r₂)
  | plus_right {s : List α} {r₁ r₂ : Regex α} :
    Matches s r₂ →
    Matches s (r₁.plus r₂)
  | mul {s₁ s₂ s : List α} {r₁ r₂ : Regex α} :
    s₁ ++ s₂ = s →
    Matches s₁ r₁ →
    Matches s₂ r₂ →
    Matches s (r₁.mul r₂)
  | star_nil {r : Regex α} :
    Matches [] r.star
  | stars {s₁ s₂ s : List α} {r : Regex α} :
    s₁ ≠ [] →
    s₁ ++ s₂ = s →
    Matches s₁ r →
    Matches s₂ r.star →
    Matches s r.star
  | group {n : String} {s k : List α} {r : Regex α} :
    Matches s r →
    Matches s (group n k r)

theorem Matches_epsilon {s : List α} :
  Matches s epsilon ↔ s = [] := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    rw [h]
    exact Matches.epsilon

theorem Matches_char {c : α} {s : List α} :
  Matches s (char c) ↔ s = [c] := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    rw [h]
    exact Matches.char

theorem Matches_plus {s : List α} {r₁ r₂ : Regex α} :
  Matches s (r₁.plus r₂) ↔ Matches s r₁ ∨ Matches s r₂ := by
  constructor
  · intro h
    cases h with
    | plus_left h => exact Or.inl h
    | plus_right h => exact Or.inr h
  · intro h
    cases h with
    | inl h => exact Matches.plus_left h
    | inr h => exact Matches.plus_right h

theorem Matches_mul {s : List α} {r₁ r₂ : Regex α} :
  Matches s (r₁.mul r₂) ↔ ∃ s₁ s₂, s₁ ++ s₂ = s ∧ Matches s₁ r₁ ∧ Matches s₂ r₂ := by
  constructor
  · intro h
    cases h with
    | mul hs h₁ h₂ => exact ⟨_, _ , hs, h₁, h₂⟩
  · intro ⟨_, _, hs, h₁, h₂⟩
    exact Matches.mul hs h₁ h₂

theorem Matches_group {n : String} {s k : List α} {r : Regex α} :
  Matches s (group n k r) ↔ Matches s r := by
  constructor
  · intro h
    cases h with
    | group h => exact h
  · intro h
    exact Matches.group h

@[simp]
def nullable : Regex α → Bool
  | emptyset => false
  | epsilon => true
  | char _ => false
  | plus r₁ r₂ => r₁.nullable || r₂.nullable
  | mul r₁ r₂ => r₁.nullable && r₂.nullable
  | star _ => true
  | group _ _ r => r.nullable

theorem nullable_iff_matches_nil {r : Regex α} :
  r.nullable ↔ Matches [] r := by
  induction r with
  | emptyset =>
    simp only [nullable, Bool.false_eq_true, false_iff]
    intro h
    nomatch h
  | epsilon =>
    simp only [nullable, true_iff]
    exact Matches.epsilon
  | char =>
    simp only [nullable, Bool.false_eq_true, false_iff]
    intro h
    nomatch h
  | plus r₁ r₂ ih₁ ih₂ =>
    simp only [nullable, Bool.or_eq_true]
    rw [ih₁, ih₂, Matches_plus]
  | mul r₁ r₂ ih₁ ih₂ =>
    simp only [nullable, Bool.and_eq_true]
    rw [ih₁, ih₂]
    constructor
    · intro ⟨h₁, h₂⟩
      exact Matches.mul (List.append_nil []) h₁ h₂
    · intro h
      cases h with
      | mul hs h₁ h₂ =>
        rw [List.append_eq_nil_iff] at hs
        rw [hs.left] at h₁
        rw [hs.right] at h₂
        exact ⟨h₁, h₂⟩
  | star r =>
    simp only [nullable, true_iff]
    exact Matches.star_nil
  | group n s r ih =>
    rw [nullable, Matches_group]
    exact ih

def markEmpty : Regex α → Regex α
  | emptyset => emptyset
  | char _ => emptyset
  | epsilon => epsilon
  | plus r₁ r₂ => plus r₁.markEmpty r₂.markEmpty
  | mul r₁ r₂ => mul r₁.markEmpty r₂.markEmpty
  | star r => star r.markEmpty
  | group n s r => group n s r.markEmpty

theorem markEmpty_nullable {r : Regex α} :
  r.markEmpty.nullable = r.nullable := by
  induction r with
  | emptyset => rfl
  | epsilon => rfl
  | char _ => rfl
  | plus r₁ r₂ ih₁ ih₂ =>
    rw [markEmpty, nullable, nullable]
    rw [ih₁, ih₂]
  | mul r₁ r₂ ih₁ ih₂ =>
    rw [markEmpty, nullable, nullable]
    rw [ih₁, ih₂]
  | star r =>
    rw [markEmpty]
    rfl
  | group n s r ih =>
    rw [markEmpty, nullable, nullable]
    exact ih

theorem markEmpty_matches_nil {r : Regex α} {s : List α} :
  Matches s r.markEmpty → s = [] := by
  intro h
  induction r generalizing s with
  | emptyset => nomatch h
  | epsilon =>
    cases h
    rfl
  | char c => nomatch h
  | plus r₁ r₂ ih₁ ih₂ =>
    cases h with
    | plus_left h => exact ih₁ h
    | plus_right h => exact ih₂ h
  | mul r₁ r₂ ih₁ ih₂ =>
    cases h with
    | mul hs h₁ h₂ =>
      rw [←hs, List.append_eq_nil_iff]
      exact ⟨ih₁ h₁, ih₂ h₂⟩
  | star r ih =>
    cases h with
    | star_nil => rfl
    | stars hn hs h₁ h₂ =>
      exact absurd (ih h₁) hn
  | group n s r ih =>
    cases h with
    | group h => exact ih h

theorem markEmpty_matches {r : Regex α} :
  Matches [] r.markEmpty ↔ Matches [] r := by
  induction r with
  | emptyset => exact ⟨nofun, nofun⟩
  | epsilon => rfl
  | char c => exact ⟨nofun, nofun⟩
  | plus r₁ r₂ ih₁ ih₂ =>
    rw [markEmpty]
    repeat rw [Matches_plus]
    rw [ih₁, ih₂]
  | mul r₁ r₂ ih₁ ih₂ =>
    constructor
    · intro h
      cases h with
      | mul hs h₁ h₂ =>
        simp at hs
        cases hs.left
        cases hs.right
        rw [ih₁] at h₁
        rw [ih₂] at h₂
        exact Matches.mul rfl h₁ h₂
    · intro h
      cases h with
      | mul hs h₁ h₂ =>
        simp at hs
        cases hs.left
        cases hs.right
        rw [←ih₁] at h₁
        rw [←ih₂] at h₂
        exact Matches.mul rfl h₁ h₂
  | star r ih =>
    rw [markEmpty]
    constructor
    · intro h
      cases h with
      | star_nil => exact Matches.star_nil
      | stars hs₁ hs h₁ h₂ =>
        simp at hs
        exact absurd hs.left hs₁
    · intro h
      cases h with
      | star_nil => exact Matches.star_nil
      | stars hs₁ hs h₁ h₂ =>
        simp at hs
        exact absurd hs.left hs₁
  | group n s r ih =>
    rw [markEmpty]
    repeat rw [Matches_group]
    exact ih

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
  | group n s r, c => group n (s ++ [c]) (r.deriv c)

theorem Matches_deriv (r : Regex α) (c : α) (s : List α) :
  Matches (c::s) r ↔ Matches s (r.deriv c) := by
  induction r generalizing s with
  | emptyset =>
    rw [deriv]
    constructor
    · intro h
      nomatch h
    · intro h
      nomatch h
  | epsilon =>
    rw [deriv]
    constructor
    · intro h
      nomatch h
    · intro h
      nomatch h
  | char c =>
    rw [Matches_char, deriv]
    rw [List.cons.injEq]
    constructor
    · intro ⟨hc, hs⟩
      rw [hc, hs]
      simp only [↓reduceIte]
      exact Matches.epsilon
    · intro h
      split at h
      · cases h
        refine ⟨?_, rfl⟩
        assumption
      · nomatch h
  | plus r₁ r₂ ih₁ ih₂ =>
    rw [deriv]
    rw [Matches_plus, Matches_plus]
    rw [ih₁, ih₂]
  | mul r₁ r₂ ih₁ ih₂ =>
    rw [deriv]
    split_ifs with hn
    · rw [Matches_plus, Matches_mul, Matches_mul, Matches_mul]
      constructor
      · intro ⟨s₁, s₂, hs, h₁, h₂⟩
        cases s₁ with
        | nil =>
          simp at hs
          cases hs
          refine Or.inr ⟨[], s, List.nil_append s, ?_, ?_⟩
          rw [←nullable_iff_matches_nil, markEmpty_nullable]
          exact hn
          rw [ih₂] at h₂
          exact h₂
        | cons x xs =>
          simp at hs
          cases hs.left
          refine Or.inl ⟨xs, s₂, hs.right, ?_, ?_⟩
          rw [ih₁] at h₁
          exact h₁
          exact h₂
      · intro h
        match h with
        | Or.inl ⟨s₁, s₂, hs, h₁, h₂⟩ =>
          rw [←ih₁] at h₁
          exact ⟨c::s₁, s₂, by simp [hs], h₁, h₂⟩
        | Or.inr ⟨s₁, s₂, hs, h₁, h₂⟩ =>
          rw [nullable_iff_matches_nil] at hn
          rw [←ih₂] at h₂
          cases (markEmpty_matches_nil h₁)
          simp at hs
          refine ⟨[], c::s₂, by simp [hs], hn, h₂⟩
    · rw [Matches_mul, Matches_mul]
      simp_rw [←ih₁]
      constructor
      · intro ⟨s₁, s₂, hs, h₁, h₂⟩
        cases s₁ with
        | nil =>
          rw [nullable_iff_matches_nil] at hn
          exact absurd h₁ hn
        | cons x xs =>
          simp at hs
          cases hs.left
          exact ⟨xs, s₂, hs.right, h₁, h₂⟩
      · intro ⟨s₁, s₂, hs, h₁, h₂⟩
        exact ⟨c::s₁, s₂, by simp [hs], h₁, h₂⟩
  | star r ih =>
    rw [deriv]
    constructor
    · intro h
      cases h with
      | @stars s₁ s₂ _ _ hs₁ hs h₁ h₂ =>
        cases s₁ with
        | nil => contradiction
        | cons x xs =>
          simp at hs
          rw [hs.left, ih] at h₁
          exact Matches.mul hs.right h₁ h₂
    · intro h
      cases h with
      | mul hs h₁ h₂ =>
        rw [←ih] at h₁
        rw [←hs, ←List.cons_append]
        exact Matches.stars (by simp) rfl h₁ h₂
  | group n k r ih =>
    rw [deriv, Matches_group, Matches_group]
    exact ih s

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
  | group n s r, hr => ⟨n, s⟩ :: extract r hr

def captures : Regex α → List α → Option (List (String × List α))
  | r, s =>
    let r' := r.derivs s
    if h : r'.nullable then some (extract r' h) else none
