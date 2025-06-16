/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Yaël Dillies, Andrew Yang
-/
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs
import Mathlib.Algebra.Order.ZeroLEOne
--import Mathlib.Algebra.Order.GroupWithZero.Canonical
--import Mathlib.Algebra.Order.GroupWithZero.Unbundled.OrderIso
--import Mathlib.Data.Finset.Lattice.Fold

/-!
Nothing to say yet
-/

namespace Inv

variable {α : Type*}

section InvNonnegClass

/-- Typeclass for whatever. -/
class InvNonneg (α : Type*) extends CommMagma α, MulZeroClass α, MulOneClass α, LinearOrder α,
    Inv α where
  protected inv_le {a b : α} (ha : 0 ≤ a) (hab : 1 ≤ a * b) : a⁻¹ ≤ b
  protected le_inv {a b : α} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a * b ≤ 1) : b ≤ a⁻¹

-- Obstacle : definition of the inverse of 0.
-- Might be interesting to restrict it to positive a, and adding variants (1 < a * b -> a⁻¹ < b...)

variable [InvNonneg α] {a b : α}

lemma inv_le (ha : 0 ≤ a) (hab : 1 ≤ a * b) : a⁻¹ ≤ b :=
  InvNonneg.inv_le ha hab

lemma le_inv (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a * b ≤ 1) : b ≤ a⁻¹ :=
  InvNonneg.le_inv ha hb hab

lemma mul_lt_one (ha : 0 ≤ a) (hab : b < a⁻¹) : a * b < 1 :=
  by_contra fun h ↦ not_le_of_gt hab (inv_le ha (not_lt.1 h))

lemma one_le_mul (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a⁻¹ < b) :
    1 < a * b :=
  by_contra fun h ↦ not_le_of_gt hab (le_inv ha hb (not_lt.1 h))

lemma inv_nonneg [ZeroLEOneClass α] (h : 0 ≤ a) :
    0 ≤ a⁻¹ :=
  le_inv h (le_refl 0) ((mul_zero a).symm ▸ zero_le_one)

lemma mono_on_nonneg' [ZeroLEOneClass α] [NeZero (1 : α)] (ha : 0 ≤ a) (hab : a ≤ b) :
    b⁻¹ ≤ a⁻¹ := by
  apply le_inv ha (inv_nonneg (ha.trans hab))
  rw [mul_comm]
  apply (mul_lt_one (inv_nonneg (ha.trans hab)) ?_).le
  sorry

lemma mono_on_nonneg [InvNonneg α] :
    MonotoneOn (fun a : α ↦ a⁻¹) {x : α | 0 ≤ x} := by
  sorry

end InvNonnegClass

end Inv

variable {α : Type*}
