import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Contrapose
import Mathlib.Data.Bool.Basic

universe u

variable {α : Type u}

inductive Regex (α :  Type u) : Type u where
  | emptyset : Regex α
  | epsilon : Regex α
  | char : α → Regex α
  | plus : Regex α → Regex α → Regex α
  | mul : Regex α → Regex α → Regex α
  | and : Regex α → Regex α → Regex α
  | star : Regex α → Regex α
  | not : Regex α → Regex α
  | group : Nat → List α → Regex α → Regex α
  deriving Repr

namespace Regex

def Matches : Regex α → List α → Prop
  | emptyset, _ => False
  | epsilon, s => s = []
  | char c, s => s = [c]
  | plus r₁ r₂, s => r₁.Matches s ∨ r₂.Matches s
  | mul r₁ r₂, s =>
    ∃ s₁ s₂, s₁ ++ s₂ = s ∧ r₁.Matches s₁ ∧ r₂.Matches s₂
  | and r₁ r₂, s => r₁.Matches s ∧ r₂.Matches s
  | star r, s => ∃ L : List (List α), L.flatten = s ∧ ∀ x ∈ L, r.Matches x
  | not r, s => ¬r.Matches s
  | group _ _ r, s => r.Matches s
termination_by r s => (r, s.length)

abbrev SubmatchEnv (α : Type u) := List (Nat × List α)

def Submatches : Regex α → List α → SubmatchEnv α → Prop
  | emptyset, _, _ => False
  | epsilon, s, Γ => s = [] ∧ Γ = []
  | char c, s, Γ => s = [c] ∧ Γ = []
  | plus r₁ r₂, s, Γ => r₁.Submatches s Γ ∨ r₂.Submatches s Γ
  | mul r₁ r₂, s, Γ =>
    ∃ s₁ s₂ Γ₁ Γ₂, s₁ ++ s₂ = s ∧ Γ₁ ++ Γ₂ = Γ ∧ r₁.Submatches s₁ Γ₁ ∧ r₂.Submatches s₂ Γ₂
  | and r₁ r₂, s, Γ =>
    ∃ Γ₁ Γ₂, Γ₁ ++ Γ₂ = Γ ∧ r₁.Submatches s Γ₁ ∧ r₂.Submatches s Γ₂
  | star r, s, Γ => ∃ L S, L.flatten = s ∧ S.flatten = Γ ∧ ∀ x ∈ List.zip L S, r.Submatches x.fst x.snd
  | not r, s, Γ => Γ = [] ∧ ∀ Γ', ¬r.Submatches s Γ'
  | group n cs r, s, Γ => ∃ Γ', (n, cs ++ s) :: Γ' = Γ ∧ r.Submatches s Γ'
termination_by r s => (r, s.length)

theorem Matches_iff_exists_Submatches {r : Regex α} {s : List α} :
  r.Matches s ↔ ∃ Γ, r.Submatches s Γ := by
  induction r generalizing s with
  | emptyset =>
    simp [Matches, Submatches]
  | epsilon =>
    simp [Matches, Submatches]
  | char c =>
    simp [Matches, Submatches]
  | plus r₁ r₁ ih₁ ih₂ =>
    simp [Matches, Submatches]
    rw [ih₁, ih₂]
    constructor
    · intro h
      match h with
      | Or.inl ⟨Γ, h⟩ =>
        exact ⟨Γ, Or.inl h⟩
      | Or.inr ⟨Γ, h⟩ =>
        exact ⟨Γ, Or.inr h⟩
    · intro ⟨Γ, h⟩
      cases h with
      | inl h => exact Or.inl ⟨Γ, h⟩
      | inr h => exact Or.inr ⟨Γ, h⟩
  | mul r₁ r₂ ih₁ ih₂ =>
    simp only [Matches, Submatches, ih₁, ih₂]
    constructor
    · intro ⟨s₁, s₂, hs, ⟨Γ₁, h₁⟩, ⟨Γ₂, h₂⟩⟩
      exact ⟨Γ₁ ++ Γ₂, s₁, s₂, Γ₁, Γ₂, hs, rfl, h₁, h₂⟩
    · intro ⟨Γ, s₁, s₂, Γ₁, Γ₂, hs, hΓ, h₁, h₂⟩
      exact ⟨s₁, s₂, hs, ⟨Γ₁, h₁⟩, ⟨Γ₂, h₂⟩⟩
  | and r₁ r₂ ih₁ ih₂ =>
    simp [Matches, Submatches]
    rw [ih₁, ih₂]
    constructor
    · intro ⟨⟨Γ₁, h₁⟩, ⟨Γ₂, h₂⟩⟩
      exact ⟨Γ₁ ++ Γ₂, Γ₁, Γ₂, rfl, h₁, h₂⟩
    · intro ⟨Γ, Γ₁, Γ₂, hΓ, h₁, h₂⟩
      exact ⟨⟨Γ₁, h₁⟩, ⟨Γ₂, h₂⟩⟩
  | star r ih =>
    simp [Matches, Submatches]
    sorry
  | not r ih =>
    simp [Matches, Submatches]
    rw [ih, not_exists]
  | group n w r ih =>
    simp [Matches, Submatches]
    rw [ih]
    constructor
    · intro ⟨Γ, h⟩
      exact ⟨(n, w ++ s) :: Γ, Γ, rfl, h⟩
    · intro ⟨Γ, Γ', hΓ, h⟩
      exact ⟨Γ', h⟩

theorem matches_epsilon_iff {s : List α} :
  Matches epsilon s ↔ s = [] := by
  rw [Matches]

theorem matches_char_iff {c : α} {s : List α} :
  Matches (char c) s ↔ s = [c] := by
  rw [Matches]

theorem matches_plus_iff {s : List α} {r₁ r₂ : Regex α} :
  Matches (r₁.plus r₂) s ↔ Matches r₁ s ∨ Matches r₂ s := by
  rw [Matches]

theorem matches_mul_iff {s : List α} {r₁ r₂ : Regex α} :
  Matches (r₁.mul r₂) s ↔ ∃ s₁ s₂, s₁ ++ s₂ = s ∧ Matches r₁ s₁ ∧ Matches r₂ s₂ := by
  rw [Matches]

-- theorem matches_star_iff {s : List α} {r : Regex α} :
--   Matches r.star s ↔ s = [] ∨ (∃ s₁ s₂, s₁ ≠ [] ∧ s₁ ++ s₂ = s ∧ Matches r s₁ ∧ Matches r.star s₂) := by
--   generalize hr : r.star = r'
--   constructor
--   · intro h
--     induction h
--     any_goals contradiction
--     · exact Or.inl rfl
--     · case stars s₁ s₂ s _ hs' h₁ h₂ ih₁ ih₂ =>
--       simp at hr
--       subst hr
--       cases s₁ with
--       | nil =>
--         simp at hs'
--         subst hs'
--         exact ih₂ rfl
--       | cons x xs =>
--         exact Or.inr ⟨x::xs, s₂, by simp, hs', h₁, h₂⟩
--   · intro h
--     subst hr
--     match h with
--     | Or.inl h =>
--       subst h
--       exact Matches.star_nil
--     | Or.inr ⟨s₁, s₂, _, hs, h₁, h₂⟩ =>
--       exact Matches.stars hs h₁ h₂

theorem matches_group_iff {n : Nat} {s k : List α} {r : Regex α} :
  Matches (group n k r) s ↔ Matches r s := by
  rw [Matches]

@[simp]
def nullable : Regex α → Bool
  | emptyset => false
  | epsilon => true
  | char _ => false
  | plus r₁ r₂ => r₁.nullable || r₂.nullable
  | mul r₁ r₂ => r₁.nullable && r₂.nullable
  | and r₁ r₂ => r₁.nullable && r₂.nullable
  | star _ => true
  | not r => ¬r.nullable
  | group _ _ r => r.nullable

theorem nullable_iff_matches_nil {r : Regex α} :
  r.nullable ↔ Matches r [] := by
  induction r with
  | emptyset =>
    simp only [Matches]
    exact ⟨nofun, nofun⟩
  | epsilon =>
    simp only [nullable, Matches]
  | char =>
    simp only [Matches]
    exact ⟨nofun, nofun⟩
  | plus r₁ r₂ ih₁ ih₂ =>
    simp only [nullable, Bool.or_eq_true]
    rw [ih₁, ih₂, Matches]
  | mul r₁ r₂ ih₁ ih₂ =>
    simp only [nullable, Bool.and_eq_true]
    rw [ih₁, ih₂, Matches]
    simp [and_assoc]
  | and r₁ r₂ ih₁ ih₂ =>
    simp [nullable, Bool.and_eq_true]
    rw [ih₁, ih₂, Matches]
  | not r ih =>
    simp [nullable]
    simp [Matches, ←ih]
  | star r ih =>
    simp [nullable, Matches]
    exact ⟨[], by simp⟩
  | group _ _ h ih =>
    simp only [nullable]
    rw [ih, Matches]

def markEmpty : Regex α → Regex α
  | emptyset => emptyset
  | epsilon => epsilon
  | char _ => emptyset
  | plus r₁ r₂ => plus r₁.markEmpty r₂.markEmpty
  | mul r₁ r₂ => mul r₁.markEmpty r₂.markEmpty
  | and r₁ r₂ => and r₁.markEmpty r₂.markEmpty
  | star r => star r.markEmpty
  | not r => not r.markEmpty
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
  | and r₁ r₂ ih₁ ih₂ =>
    rw [markEmpty, nullable, nullable]
    rw [ih₁, ih₂]
  | star r =>
    rw [markEmpty]
    rfl
  | not r ih =>
    rw [markEmpty, nullable, nullable, ih]
  | group n s r ih =>
    rw [markEmpty, nullable, nullable]
    exact ih

-- theorem markEmpty_matches_nil {r : Regex α} {s : List α} :
--   Matches r.markEmpty s → s = [] := by
--   intro h
--   induction r generalizing s with
--   | emptyset => nomatch h
--   | epsilon =>
--     cases h
--     rfl
--   | char c => nomatch h
--   | plus r₁ r₂ ih₁ ih₂ =>
--     cases h with
--     | plus_left h => exact ih₁ h
--     | plus_right h => exact ih₂ h
--   | mul r₁ r₂ ih₁ ih₂ =>
--     cases h with
--     | mul hs h₁ h₂ =>
--       rw [←hs, List.append_eq_nil_iff]
--       exact ⟨ih₁ h₁, ih₂ h₂⟩
--   | star r ih =>
--     rw [markEmpty, matches_star_iff] at h
--     match h with
--     | Or.inl h => exact h
--     | Or.inr ⟨s₁, s₂, hs₁, hs, h₁, h₂⟩ =>
--       exact absurd (ih h₁) hs₁
--   | group n s r ih =>
--     cases h with
--     | group h => exact ih h

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
  | and r₁ r₂, c => (r₁.deriv c).and (r₂.deriv c)
  | star r, c => (r.deriv c).mul r.star
  | not r, c => not (r.deriv c)
  | group n s r, c => group n (s ++ [c]) (r.deriv c)

-- theorem matches_deriv_mul_iff {r₁ r₂ : Regex α} {c : α} {s : List α} :
--   Matches ((r₁.mul r₂).deriv c) s ↔ Matches ((r₁.deriv c).mul r₂) s ∨
--   (r₁.nullable ∧ Matches (r₁.markEmpty.mul (r₂.deriv c)) s) := by
--   rw [deriv]
--   split
--   · case isTrue hn =>
--     rw [matches_plus_iff]
--     simp [hn]
--   · case isFalse hn =>
--     simp [hn]

-- theorem Matches_deriv {r : Regex α} {c : α} {s : List α} :
--   Matches r (c::s) ↔ Matches (r.deriv c) s := by
--   induction r generalizing s with
--   | emptyset => exact ⟨nofun, nofun⟩
--   | epsilon => exact ⟨nofun, nofun⟩
--   | char c =>
--     rw [matches_char_iff, deriv]
--     rw [List.cons.injEq]
--     constructor
--     · intro ⟨hc, hs⟩
--       rw [hc, hs]
--       simp only [↓reduceIte]
--       exact Matches.epsilon
--     · intro h
--       split at h
--       · cases h
--         refine ⟨?_, rfl⟩
--         assumption
--       · nomatch h
--   | plus r₁ r₂ ih₁ ih₂ =>
--     rw [deriv]
--     rw [matches_plus_iff, matches_plus_iff]
--     rw [ih₁, ih₂]
--   | mul r₁ r₂ ih₁ ih₂ =>
--     rw [matches_deriv_mul_iff]
--     repeat rw [matches_mul_iff]
--     constructor
--     · intro ⟨s₁, s₂, hs, h₁, h₂⟩
--       rw [List.append_eq_cons_iff] at hs
--       match hs with
--       | Or.inl ⟨hs₁, hs₂⟩ =>
--         subst hs₁ hs₂
--         rw [←nullable_iff_matches_nil] at h₁
--         rw [←markEmpty_nullable, nullable_iff_matches_nil] at h₁
--         rw [←markEmpty_nullable, nullable_iff_matches_nil]
--         exact Or.inr ⟨h₁, [], s, rfl, h₁, ih₂.mp h₂⟩
--       | Or.inr ⟨as, hs₁, hs⟩ =>
--         rw [hs₁, ih₁] at h₁
--         exact Or.inl ⟨as, s₂, hs.symm, h₁, h₂⟩
--     · intro h
--       match h with
--       | Or.inl ⟨s₁, s₂, hs, h₁, h₂⟩ =>
--         exact ⟨c::s₁, s₂, by simp [hs], ih₁.mpr h₁, h₂⟩
--       | Or.inr ⟨hn, s₁, s₂, hs, h₁, h₂⟩ =>
--         rw [nullable_iff_matches_nil] at hn
--         rw [markEmpty_matches_nil h₁] at hs
--         subst hs
--         exact ⟨[], c::s₂, rfl, hn, ih₂.mpr h₂⟩
--   | star r ih =>
--     rw [deriv, matches_star_iff, matches_mul_iff]
--     simp [←ih]
--     constructor
--     · intro ⟨s₁, hs₁, s₂, hs, h₁, h₂⟩
--       cases s₁ with
--       | nil => contradiction
--       | cons x xs =>
--         simp at hs
--         rw [hs.left] at h₁
--         exact ⟨xs, s₂, hs.right, h₁, h₂⟩
--     · intro ⟨s₁, s₂, hs, h₁, h₂⟩
--       exact ⟨c::s₁, by simp, s₂, by simp [hs], h₁, h₂⟩
--   | group n k r ih =>
--     rw [deriv, matches_group_iff, matches_group_iff]
--     exact ih

@[simp]
def derivs : Regex α → List α → Regex α
  | r, [] => r
  | r, c::s => (r.deriv c).derivs s

-- theorem Matches_derivs {r : Regex α} {s : List α} :
--   r.Matches s ↔ (r.derivs s).Matches [] := by
--   induction s generalizing r with
--   | nil => rfl
--   | cons x xs ih =>
--     rw [Matches_deriv, ih]
--     rfl

def extract : (r : Regex α) → r.nullable → SubmatchEnv α
  | epsilon, _ => []
  | plus r₁ r₂, hr =>
    if hr₁ : r₁.nullable
    then extract r₁ hr₁
    else
      have hr₂ := (Bool.or_eq_true_iff.mp hr).resolve_left hr₁
      extract r₂ hr₂
  | mul r₁ r₂, hr =>
    have hr₁ := Bool.and_elim_left hr
    have hr₂ := Bool.and_elim_right hr
    extract r₁ hr₁ ++ extract r₂ hr₂
  | and r₁ r₂, hr =>
    have hr₁ := Bool.and_elim_left hr
    have hr₂ := Bool.and_elim_right hr
    extract r₁ hr₁ ++ extract r₂ hr₂
  | star _, _ => []
  | not _, _ => []
  | group n s r, hr => ⟨n, s⟩ :: extract r hr

def captures : Regex α → List α → Option (SubmatchEnv α)
  | r, s =>
    let r' := r.derivs s
    if h : r'.nullable then some (extract r' h) else none
