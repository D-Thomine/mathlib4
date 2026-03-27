/-
Copyright (c) 2026 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
module

public import Mathlib.Data.Real.Basic

/-!
Fichier de travail pour exposé à Brest le lundi 30 mars 2026.
-/
@[expose] public section

namespace Brest

/-- Une suite de réels `u` converge vers `l` si `∀ ε > 0, ∃ N, ∀ n ≥ N, |u_n - l| ≤ ε`. -/
def seq_limit (u : ℕ → ℝ) (l : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

/-- Une fonction `f : ℝ → ℝ` est continue en `x₀` si
`∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ ⇒ |f(x) - f(x₀)| ≤ ε`. -/
def continuous_at (f : ℝ → ℝ) (x₀ : ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

-- Commencer par une démonstration papier.

lemma limit_comp (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ) (hu : seq_limit u x₀) (hf : continuous_at f x₀) :
    seq_limit (f ∘ u) (f x₀) := by
  sorry

lemma limit_comp1 (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ) (hu : seq_limit u x₀) (hf : continuous_at f x₀) :
    seq_limit (f ∘ u) (f x₀) := by
  --intros ε hε
  --obtain ⟨δ, δ_pos, Hf⟩ := hf ε hε
  --obtain ⟨N, Hu⟩ := hu δ δ_pos
  --use N
  --intros n hn
  --apply Hf
  --apply Hu n hn
  sorry

lemma limit_comp2 (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ) (hu : seq_limit u x₀) (hf : continuous_at f x₀) :
    seq_limit (f ∘ u) (f x₀) := by
  intros ε hε
  obtain ⟨δ, δ_pos, Hf⟩ := hf ε hε
  obtain ⟨N, Hu⟩ := hu δ δ_pos
  -- exact ⟨N, fun n hn ↦ (Hf _) (Hu n hn)⟩
  sorry

lemma limit_comp3 (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ) (hu : seq_limit u x₀) (hf : continuous_at f x₀) :
    seq_limit (f ∘ u) (f x₀) := by
  intros ε hε
  obtain ⟨δ, δ_pos, Hf⟩ := hf ε hε
  obtain ⟨N, Hu⟩ := hu δ δ_pos
  --use N
  --solve_by_elim
  sorry

/-- L'accès à Mathlib peut trivialiser de nombreuses démonstrations. -/
lemma exists_real_gt1 : ∀ x : ℝ, ∃ y, x > y := by
  --intro x
  --use x+1
  --exact lt_add_one x
  sorry

lemma exists_real_gt : ∀ x : ℝ, ∃ y, x < y :=
  exists_gt

/-- L'état tactique tend à favoriser un raisonnement par manipulation du but. -/
lemma implication {P Q : Prop} (h : P) (h' : P → Q) : Q := by
  apply h'
  exact h

/-- Manipulations sans tactiques. -/
lemma a_remarkable_identity (a b : ℝ) (h : a ^ 2 + 2 * a * b + b ^ 2 = 1) : (a + b) ^ 2 = 1 := by
  rw [pow_two, add_mul, mul_add, mul_add, ← pow_two, ← pow_two, mul_comm b a, add_assoc (a^2),
    ← add_assoc (a*b), ← two_mul, ← add_assoc, ← mul_assoc]
  exact h
end Brest
