import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.SimpRw
import Mathlib.Data.Bool.Basic

universe u

variable {α : Type u}

inductive Regex (α :  Type u) : Type u where
  | emptyset : Regex α
  | epsilon : Regex α
  | char : α → Regex α
  | plus : Regex α → Regex α → Regex α
  | mul : Regex α → Regex α → Regex α
  | star : Regex α → Regex α
  | group : Nat → List α → Regex α → Regex α
  deriving Repr

namespace Regex

inductive Matches : Regex α → List α → Prop
  | epsilon : Matches epsilon []
  | char {c : α} : Matches (char c) [c]
  | plus_left {s : List α} {r₁ r₂ : Regex α} :
    Matches r₁ s →
    Matches (r₁.plus r₂) s
  | plus_right {s : List α} {r₁ r₂ : Regex α} :
    Matches r₂ s →
    Matches (r₁.plus r₂) s
  | mul {s₁ s₂ s : List α} {r₁ r₂ : Regex α} :
    s₁ ++ s₂ = s →
    Matches r₁ s₁ →
    Matches r₂ s₂ →
    Matches (r₁.mul r₂) s
  | star_nil {r : Regex α} :
    Matches r.star []
  | stars {s₁ s₂ s : List α} {r : Regex α} :
    s₁ ++ s₂ = s →
    Matches r s₁ →
    Matches r.star s₂ →
    Matches r.star s
  | group {n : Nat} {s cs : List α} {r : Regex α} :
    Matches r s →
    Matches (group n cs r) s

abbrev SubmatchEnv (α : Type u) := List (Nat × List α)

inductive Submatches : List α → Regex α → SubmatchEnv α → Prop
  | epsilon : Submatches [] epsilon []
  | char {c : α} : Submatches [c] (char c) []
  | left {s : List α} {r₁ r₂ : Regex α} {Γ : SubmatchEnv α} :
    Submatches s r₁ Γ →
    Submatches s (r₁.plus r₂) Γ
  | right {s : List α} {r₁ r₂ : Regex α} {Γ : SubmatchEnv α} :
    Submatches s r₂ Γ →
    Submatches s (r₁.plus r₂) Γ
  | mul {s s₁ s₂ : List α} {r₁ r₂ : Regex α} {Γ Γ₁ Γ₂ : SubmatchEnv α} :
    s₁ ++ s₂ = s →
    Γ₁ ++ Γ₂ = Γ →
    Submatches s₁ r₁ Γ₁ →
    Submatches s₂ r₂ Γ₂ →
    Submatches s (r₁.mul r₂) Γ
  | star_nil {r : Regex α} : Submatches [] r.star []
  | stars {s s₁ s₂ : List α} {r : Regex α} {Γ Γ₁ Γ₂ : SubmatchEnv α} :
    s₁ ++ s₂ = s →
    Γ₁ ++ Γ₂ = Γ →
    Submatches s₁ r Γ₁ →
    Submatches s₂ r.star Γ₂ →
    Submatches s r.star Γ
  | group {n : Nat} {s cs : List α} {r : Regex α} {Γ : SubmatchEnv α} :
    Submatches s r Γ →
    Submatches s (group n cs r) ((n, cs ++ s) :: Γ)

theorem Submatches.matches {r : Regex α} {s : List α} {Γ : SubmatchEnv α} (h : Submatches s r Γ) :
  r.Matches s := by
  induction h with
  | epsilon => exact Matches.epsilon
  | char => exact Matches.char
  | left h ih => exact Matches.plus_left ih
  | right h ih => exact Matches.plus_right ih
  | mul hs _ h₁ h₂ ih₁ ih₂ =>
    exact Matches.mul hs ih₁ ih₂
  | star_nil => exact Matches.star_nil
  | stars hs _ h₁ h₂ ih₁ ih₂ =>
    exact Matches.stars hs ih₁ ih₂
  | group h ih => exact Matches.group ih

theorem Matches.exists_submatches {r : Regex α} {s : List α} (h : Matches r s) :
  ∃ Γ, Submatches s r Γ := by
  induction h with
  | epsilon => exact ⟨[], Submatches.epsilon⟩
  | char => exact ⟨[], Submatches.char⟩
  | plus_left h ih =>
    rcases ih with ⟨Γ, ih⟩
    exact ⟨Γ, Submatches.left ih⟩
  | plus_right h ih =>
    rcases ih with ⟨Γ, ih⟩
    exact ⟨Γ, Submatches.right ih⟩
  | mul hs h₁ h₂ ih₁ ih₂ =>
    rcases ih₁ with ⟨Γ₁, ih₁⟩
    rcases ih₂ with ⟨Γ₂, ih₂⟩
    exact ⟨Γ₁ ++ Γ₂, Submatches.mul hs rfl ih₁ ih₂⟩
  | star_nil =>
    exact ⟨[], Submatches.star_nil⟩
  | stars hs h₁ h₂ ih₁ ih₂ =>
    rcases ih₁ with ⟨Γ₁, ih₁⟩
    rcases ih₂ with ⟨Γ₂, ih₂⟩
    exact ⟨Γ₁ ++ Γ₂, Submatches.stars hs rfl ih₁ ih₂⟩
  | @group n s cs r h ih =>
    rcases ih with ⟨Γ, ih⟩
    exact ⟨(n, cs ++ s) :: Γ, Submatches.group ih⟩

theorem matches_epsilon_iff {s : List α} :
  Matches epsilon s ↔ s = [] := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    rw [h]
    exact Matches.epsilon

theorem matches_char_iff {c : α} {s : List α} :
  Matches (char c) s ↔ s = [c] := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    rw [h]
    exact Matches.char

theorem matches_plus_iff {s : List α} {r₁ r₂ : Regex α} :
  Matches (r₁.plus r₂) s ↔ Matches r₁ s ∨ Matches r₂ s := by
  constructor
  · intro h
    cases h with
    | plus_left h => exact Or.inl h
    | plus_right h => exact Or.inr h
  · intro h
    cases h with
    | inl h => exact Matches.plus_left h
    | inr h => exact Matches.plus_right h

theorem matches_mul_iff {s : List α} {r₁ r₂ : Regex α} :
  Matches (r₁.mul r₂) s ↔ ∃ s₁ s₂, s₁ ++ s₂ = s ∧ Matches r₁ s₁ ∧ Matches r₂ s₂ := by
  constructor
  · intro h
    cases h with
    | mul hs h₁ h₂ => exact ⟨_, _ , hs, h₁, h₂⟩
  · intro ⟨_, _, hs, h₁, h₂⟩
    exact Matches.mul hs h₁ h₂

theorem matches_star_iff {s : List α} {r : Regex α} :
  Matches r.star s ↔ s = [] ∨ (∃ s₁ s₂, s₁ ≠ [] ∧ s₁ ++ s₂ = s ∧ Matches r s₁ ∧ Matches r.star s₂) := by
  generalize hr : r.star = r'
  constructor
  · intro h
    induction h
    any_goals contradiction
    · exact Or.inl rfl
    · case stars s₁ s₂ s _ hs' h₁ h₂ ih₁ ih₂ =>
      simp at hr
      subst hr
      cases s₁ with
      | nil =>
        simp at hs'
        subst hs'
        exact ih₂ rfl
      | cons x xs =>
        exact Or.inr ⟨x::xs, s₂, by simp, hs', h₁, h₂⟩
  · intro h
    subst hr
    match h with
    | Or.inl h =>
      subst h
      exact Matches.star_nil
    | Or.inr ⟨s₁, s₂, _, hs, h₁, h₂⟩ =>
      exact Matches.stars hs h₁ h₂

theorem matches_group_iff {n : Nat} {s k : List α} {r : Regex α} :
  Matches (group n k r) s ↔ Matches r s := by
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
  r.nullable ↔ Matches r [] := by
  induction r with
  | emptyset => exact ⟨nofun, nofun⟩
  | epsilon =>
    simp only [nullable, true_iff]
    exact Matches.epsilon
  | char => exact ⟨nofun, nofun⟩
  | plus r₁ r₂ ih₁ ih₂ =>
    simp only [nullable, Bool.or_eq_true]
    rw [ih₁, ih₂, matches_plus_iff]
  | mul r₁ r₂ ih₁ ih₂ =>
    simp only [nullable, Bool.and_eq_true]
    rw [ih₁, ih₂, matches_mul_iff]
    simp [and_assoc]
  | star r =>
    simp only [nullable, true_iff]
    exact Matches.star_nil
  | group _ _ h ih =>
    simp only [nullable]
    rw [ih, matches_group_iff]

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
  Matches r.markEmpty s → s = [] := by
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
    rw [markEmpty, matches_star_iff] at h
    match h with
    | Or.inl h => exact h
    | Or.inr ⟨s₁, s₂, hs₁, hs, h₁, h₂⟩ =>
      exact absurd (ih h₁) hs₁
  | group n s r ih =>
    cases h with
    | group h => exact ih h

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

theorem matches_deriv_mul_iff {r₁ r₂ : Regex α} {c : α} {s : List α} :
  Matches ((r₁.mul r₂).deriv c) s ↔ Matches ((r₁.deriv c).mul r₂) s ∨
  (r₁.nullable ∧ Matches (r₁.markEmpty.mul (r₂.deriv c)) s) := by
  rw [deriv]
  split
  · case isTrue hn =>
    rw [matches_plus_iff]
    simp [hn]
  · case isFalse hn =>
    simp [hn]

theorem Matches_deriv {r : Regex α} {c : α} {s : List α} :
  Matches r (c::s) ↔ Matches (r.deriv c) s := by
  induction r generalizing s with
  | emptyset => exact ⟨nofun, nofun⟩
  | epsilon => exact ⟨nofun, nofun⟩
  | char c =>
    rw [matches_char_iff, deriv]
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
    rw [matches_plus_iff, matches_plus_iff]
    rw [ih₁, ih₂]
  | mul r₁ r₂ ih₁ ih₂ =>
    rw [matches_deriv_mul_iff]
    repeat rw [matches_mul_iff]
    constructor
    · intro ⟨s₁, s₂, hs, h₁, h₂⟩
      rw [List.append_eq_cons_iff] at hs
      match hs with
      | Or.inl ⟨hs₁, hs₂⟩ =>
        subst hs₁ hs₂
        rw [←nullable_iff_matches_nil] at h₁
        rw [←markEmpty_nullable, nullable_iff_matches_nil] at h₁
        rw [←markEmpty_nullable, nullable_iff_matches_nil]
        exact Or.inr ⟨h₁, [], s, rfl, h₁, ih₂.mp h₂⟩
      | Or.inr ⟨as, hs₁, hs⟩ =>
        rw [hs₁, ih₁] at h₁
        exact Or.inl ⟨as, s₂, hs.symm, h₁, h₂⟩
    · intro h
      match h with
      | Or.inl ⟨s₁, s₂, hs, h₁, h₂⟩ =>
        exact ⟨c::s₁, s₂, by simp [hs], ih₁.mpr h₁, h₂⟩
      | Or.inr ⟨hn, s₁, s₂, hs, h₁, h₂⟩ =>
        rw [nullable_iff_matches_nil] at hn
        rw [markEmpty_matches_nil h₁] at hs
        subst hs
        exact ⟨[], c::s₂, rfl, hn, ih₂.mpr h₂⟩
  | star r ih =>
    rw [deriv, matches_star_iff, matches_mul_iff]
    simp [←ih]
    constructor
    · intro ⟨s₁, hs₁, s₂, hs, h₁, h₂⟩
      cases s₁ with
      | nil => contradiction
      | cons x xs =>
        simp at hs
        rw [hs.left] at h₁
        exact ⟨xs, s₂, hs.right, h₁, h₂⟩
    · intro ⟨s₁, s₂, hs, h₁, h₂⟩
      exact ⟨c::s₁, by simp, s₂, by simp [hs], h₁, h₂⟩
  | group n k r ih =>
    rw [deriv, matches_group_iff, matches_group_iff]
    exact ih

@[simp]
def derivs : Regex α → List α → Regex α
  | r, [] => r
  | r, c::s => (r.deriv c).derivs s

theorem Matches_derivs {r : Regex α} {s : List α} :
  r.Matches s ↔ (r.derivs s).Matches [] := by
  induction s generalizing r with
  | nil => rfl
  | cons x xs ih =>
    rw [Matches_deriv, ih]
    rfl

def extract : (r : Regex α) → r.nullable → SubmatchEnv α
  | epsilon, _ => []
  | plus r₁ r₂, hr =>
    if hr₁ : r₁.nullable
    then extract r₁ hr₁
    else
      have hr₂ := (Bool.or_eq_true_iff.mp hr).resolve_left hr₁
      extract r₂ hr₂
  | mul r₁ r₂, hr => by
    have hr₁ := Bool.and_elim_left hr
    have hr₂ := Bool.and_elim_right hr
    exact extract r₁ hr₁ ++ extract r₂ hr₂
  | star r, _ => []
  | group n s r, hr => ⟨n, s⟩ :: extract r hr

def captures : Regex α → List α → Option (SubmatchEnv α)
  | r, s =>
    let r' := r.derivs s
    if h : r'.nullable then some (extract r' h) else none
