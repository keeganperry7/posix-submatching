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
    s₁ ++ s₂ = s →
    Matches s₁ r →
    Matches s₂ r.star →
    Matches s r.star
  | group {n : Nat} {s cs : List α} {r : Regex α} :
    Matches s r →
    Matches s (group n cs r)

inductive Submatches : List α → Regex α → List (Nat × List α) → Prop
  | epsilon : Submatches [] epsilon []
  | char {c : α} : Submatches [c] (char c) []
  | left {s : List α} {r₁ r₂ : Regex α} {Γ : List (Nat × List α)} :
    Submatches s r₁ Γ →
    Submatches s (r₁.plus r₂) Γ
  | right {s : List α} {r₁ r₂ : Regex α} {Γ : List (Nat × List α)} :
    Submatches s r₂ Γ →
    Submatches s (r₁.plus r₂) Γ
  | mul {s s₁ s₂ : List α} {r₁ r₂ : Regex α} {Γ Γ₁ Γ₂ : List (Nat × List α)} :
    s₁ ++ s₂ = s →
    Γ₁ ++ Γ₂ = Γ →
    Submatches s₁ r₁ Γ₁ →
    Submatches s₂ r₂ Γ₂ →
    Submatches s (r₁.mul r₂) Γ
  | star_nil {r : Regex α} : Submatches [] r.star []
  | stars {s s₁ s₂ : List α} {r : Regex α} {Γ Γ₁ Γ₂ : List (Nat × List α)} :
    s₁ ++ s₂ = s →
    Γ₁ ++ Γ₂ = Γ →
    Submatches s₁ r Γ₁ →
    Submatches s₂ r.star Γ₂ →
    Submatches s r.star Γ
  | group {n : Nat} {s cs : List α} {r : Regex α} {Γ : List (Nat × List α)} :
    Submatches s r Γ →
    Submatches s (group n cs r) ((n, cs ++ s) :: Γ)

example :
  Submatches
    -- "aba"
    ['a', 'b', 'a']
    -- (₁a + b)*
    (star (group 1 [] (plus (char 'a') (char 'b'))))
    -- {1 ↦ "a", 1 ↦ "b", 1 ↦ "a"}
    [(1, ['a']), (1, ['b']), (1, ['a'])] :=
    Submatches.stars rfl rfl
      (Submatches.group (Submatches.left Submatches.char))
      (Submatches.stars rfl rfl
        (Submatches.group (Submatches.right Submatches.char))
        (Submatches.stars rfl rfl
          (Submatches.group (Submatches.left Submatches.char))
          (Submatches.star_nil)))

theorem Submatches_Matches {r : Regex α} {s : List α} {Γ : List (Nat × List α)} (h : Submatches s r Γ) :
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

theorem Matches_Submatches {r : Regex α} {s : List α} (h : Matches s r) :
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

theorem Matches_star {s : List α} {r : Regex α} :
  Matches s r.star ↔ s = [] ∨ (∃ s₁ s₂, s₁ ≠ [] ∧ s₁ ++ s₂ = s ∧ Matches s₁ r ∧ Matches s₂ r.star) := by
  generalize hr : r.star = r'
  constructor
  · intro h
    induction h with
    | epsilon => nomatch hr
    | char => nomatch hr
    | plus_left => nomatch hr
    | plus_right => nomatch hr
    | mul => nomatch hr
    | star_nil => exact Or.inl rfl
    | @stars s₁ s₂ s _ hs' h₁ h₂ ih₁ ih₂ =>
      simp at hr
      subst hr
      cases s₁ with
      | nil =>
        simp at hs'
        subst hs'
        exact ih₂ rfl
      | cons x xs =>
        exact Or.inr ⟨x::xs, s₂, by simp, hs', h₁, h₂⟩
    | group => nomatch hr
  · intro h
    subst hr
    match h with
    | Or.inl h =>
      subst h
      exact Matches.star_nil
    | Or.inr ⟨s₁, s₂, _, hs, h₁, h₂⟩ =>
      exact Matches.stars hs h₁ h₂

theorem Matches_group {n : Nat} {s k : List α} {r : Regex α} :
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
  | emptyset => exact ⟨nofun, nofun⟩
  | epsilon =>
    simp only [nullable, true_iff]
    exact Matches.epsilon
  | char => exact ⟨nofun, nofun⟩
  | plus r₁ r₂ ih₁ ih₂ =>
    simp only [nullable, Bool.or_eq_true]
    rw [ih₁, ih₂, Matches_plus]
  | mul r₁ r₂ ih₁ ih₂ =>
    simp only [nullable, Bool.and_eq_true]
    rw [ih₁, ih₂, Matches_mul]
    simp [and_assoc]
  | star r =>
    simp only [nullable, true_iff]
    exact Matches.star_nil
  | group _ _ h ih =>
    simp only [nullable]
    rw [ih, Matches_group]

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
    rw [markEmpty, Matches_star] at h
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

theorem Matches_deriv (r : Regex α) (c : α) (s : List α) :
  Matches (c::s) r ↔ Matches s (r.deriv c) := by
  induction r generalizing s with
  | emptyset => exact ⟨nofun, nofun⟩
  | epsilon => exact ⟨nofun, nofun⟩
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
      rw [Matches_star] at h
      simp at h
      rcases h with ⟨s₁, hs₁, s₂, hs, h₁, h₂⟩
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
        exact Matches.stars rfl h₁ h₂
  | group n k r ih =>
    rw [deriv, Matches_group, Matches_group]
    exact ih s

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

def extract : (r : Regex α) → r.nullable → List (Nat × List α)
  | epsilon, _ => []
  | plus r₁ r₂, hr =>
    if hr₁ : r₁.nullable
      then extract r₁ hr₁
      else
        have hr₂ := Or.resolve_left (Bool.or_eq_true _ _▸ hr) hr₁
        extract r₂ hr₂
  | mul r₁ r₂, hr => by
    have hr₁ := Bool.and_elim_left hr
    have hr₂ := Bool.and_elim_right hr
    exact extract r₁ hr₁ ++ extract r₂ hr₂
  | star r, _ => []
  | group n s r, hr => ⟨n, s⟩ :: extract r hr

def captures : Regex α → List α → Option (List (Nat × List α))
  | r, s =>
    let r' := r.derivs s
    if h : r'.nullable then some (extract r' h) else none
