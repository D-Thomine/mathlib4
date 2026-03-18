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

lemma test_pedestre : ∀ x : ℝ, ∃ y : ℝ, x < y := by
  --intro x
  --use x + 1
  --exact lt_add_one x
  sorry

-- #check lt_add_one

lemma test_tactique : ∀ x : ℝ, ∃ y : ℝ, x < y := by
  --intro x
  --use x + 1
  --simp
  sorry

lemma test_terme_preuve : ∀ x : ℝ, ∃ y : ℝ, x < y :=
  --fun x ↦ ⟨x+1, lt_add_one x⟩
  by sorry

lemma test_bibliotheque : ∀ x : ℝ, ∃ y : ℝ, x < y :=
  -- exists_gt
  by sorry

end Brest
