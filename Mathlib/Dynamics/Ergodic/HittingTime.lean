/-
Copyright (c) 2026 Dalien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Conservative systems

In this file we define `f : α → α` to be a *conservative* system w.r.t. a measure `μ` if `f` is
non-singular (`MeasureTheory.QuasiMeasurePreserving`) and for every measurable set `s` of
positive measure at least one point `x ∈ s` returns back to `s` after some number of iterations of
`f`. There are several properties that look like they are stronger than this one but actually follow
from it:

* `MeasureTheory.Conservative.frequently_measure_inter_ne_zero`,
  `MeasureTheory.Conservative.exists_gt_measure_inter_ne_zero`: if `μ s ≠ 0`, then for infinitely
  many `n`, the measure of `s ∩ f^[n] ⁻¹' s` is positive.

* `MeasureTheory.Conservative.measure_mem_forall_ge_image_notMem_eq_zero`,
  `MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem`: a.e. every point of `s` visits `s`
  infinitely many times (Poincaré recurrence theorem).

We also prove the topological Poincaré recurrence theorem
`MeasureTheory.Conservative.ae_frequently_mem_of_mem_nhds`. Let `f : α → α` be a conservative
dynamical system on a topological space with second countable topology and measurable open
sets. Then almost every point `x : α` is recurrent: it visits every neighborhood `s ∈ 𝓝 x`
infinitely many times.

## Tags

conservative dynamical system, Poincare recurrence theorem
-/

public section

noncomputable section

namespace Recurrence

open Filter Measurable MeasureTheory Nat Set

open Measure


lemma _root_.Filter.EventuallyEq.countable_preimage {α β : Type*} {l : Filter α}
    [CountableInterFilter l] [Countable β] {f g : α → β}
    (h : ∀ x, { y | f y = x } =ᶠ[l] { y | g y = x }) :
    f =ᶠ[l] g := by
  apply eventuallyEq_iff_exists_mem.2
  refine ⟨⋂ x, univ \ symmDiff { y | f y = x } { y | g y = x }, ?_, ?_⟩
  · refine countable_iInter_mem.2 fun x ↦ ?_
    filter_upwards [eventuallyEq_set.1 (h x)]
    intro y hy
    simp only [Set.mem_sdiff, mem_univ, mem_symmDiff, mem_setOf_eq, not_or, not_and, not_not,
      true_and] at hy ⊢
    exact ⟨hy.1, hy.2⟩
  · intro y hy
    simp only [symmDiff, sup_eq_union, mem_iInter, Set.mem_sdiff, mem_univ, mem_union, mem_setOf_eq,
      not_or, not_and, not_not, true_and] at hy ⊢
    exact (hy (g y)).2 (by rfl)


variable {α : Type*} {f : α → α} {s : Set α} {x : α}

/-- `HittingTime f s` is the function which to each point `x` associates the first positive time `n`
at which the iterate `f^[n] x` belongs to `s`. By the convention `sInf ∅ = 0`, if the positive orbit
of `x` never hits `s`, then `HittingTime f s x = 0`. -/
def HittingTime (f : α → α) (s : Set α) :=
    fun x ↦ sInf {n : ℕ | n ≠ 0 ∧ f^[n] x ∈ s}

lemma hittingTime_eq_zero_iff_forall :
    HittingTime f s x = 0 ↔ ∀ n ≠ 0, f^[n] x ∉ s := by
  simp [HittingTime, Set.eq_empty_iff_forall_notMem]

lemma hittingTime_pos_iff_exists :
    HittingTime f s x ≠ 0 ↔ ∃ n ≠ 0, f^[n] x ∈ s := by
  rw [← not_iff_not]
  simp [hittingTime_eq_zero_iff_forall]

lemma not_mem_iterate_of_lt_hittingTime {n : ℕ} (h₀ : n ≠ 0) (h : n < HittingTime f s x) :
    f^[n] x ∉ s :=
  fun hx ↦ notMem_of_lt_sInf h ⟨h₀, hx⟩

lemma mem_iterate_of_hittingTime (h : HittingTime f s x ≠ 0) :
    f^[HittingTime f s x] x ∈ s :=
  (sInf_mem (nonempty_of_pos_sInf (pos_of_ne_zero h))).2

lemma hittingTime_eq_pos_iff {n : ℕ} (h₀ : n ≠ 0) :
    HittingTime f s x = n ↔ (∀ k ∈ Ioo 0 n, f^[k] x ∉ s) ∧ f^[n] x ∈ s := by
  simp only [mem_Ioo, and_imp]
  constructor <;> intro h
  · rw [← h] at h₀ ⊢
    exact ⟨fun k k₀ kn ↦ not_mem_iterate_of_lt_hittingTime k₀.ne.symm kn,
      mem_iterate_of_hittingTime h₀⟩
  · refine eq_iff_le_not_lt.2 ⟨Nat.sInf_le ⟨h₀, h.2⟩, fun hn ↦ ?_⟩
    have ht₀ : 0 < HittingTime f s x := pos_of_ne_zero (hittingTime_pos_iff_exists.2 ⟨n, h₀, h.2⟩)
    exact h.1 (HittingTime f s x) ht₀ hn (mem_iterate_of_hittingTime ht₀.ne.symm)

lemma hittingTime_zero_set_eq_iInter :
    {x | HittingTime f s x = 0} = (⋂ k ≠ 0, f^[k] ⁻¹' sᶜ) := by
  ext x
  simp [hittingTime_eq_zero_iff_forall]

lemma hittingTime_pos_set_eq_iInter_inter {n : ℕ} (h : n ≠ 0) :
    {x | HittingTime f s x = n} = (⋂ k ∈ Ioo 0 n, f^[k] ⁻¹' sᶜ) ∩ f^[n] ⁻¹' s := by
  ext x
  simp [hittingTime_eq_pos_iff h]

/-- `HittingMap f s` is the function which to each point `x` associates the point at which the
positive orbit of `x` first hits `s`. By the convention `sInf ∅ = 0`, if the positive orbit
of `x` never hits `s`, then `HittingMap f s x = x`. -/
def HittingMap (f : α → α) (s : Set α) :=
    fun x ↦ f^[HittingTime f s x] x

lemma hittingMap_apply : HittingMap f s x = f^[HittingTime f s x] x := by rfl

lemma hittingMap_eq_self_of_hittingTime_zero (h : HittingTime f s x = 0) :
    HittingMap f s x = x := by
  simp [HittingMap, h]

lemma hittingMap_mem_iff :
    HittingMap f s x ∈ s ↔ HittingTime f s x ≠ 0 ∨ x ∈ s := by
  by_cases h : HittingTime f s x = 0
  · simp [h, hittingMap_eq_self_of_hittingTime_zero h]
  · simp only [ne_eq, h, not_false_eq_true, true_or, iff_true]
    exact mem_iterate_of_hittingTime h

lemma hittingMap_mem_of_hittingTime_pos (h : HittingTime f s x ≠ 0) :
    HittingMap f s x ∈ s :=
  hittingMap_mem_iff.2 (Or.inl h)

lemma mapsTo_hittingMap (f : α → α) (s : Set α) :
    MapsTo (HittingMap f s) s s :=
  fun _ h ↦hittingMap_mem_iff.2 (Or.inr h)

lemma hittingMap_preimage (f : α → α) (s t : Set α) :
    (HittingMap f s) ⁻¹' t = ⋃ n, {x | HittingTime f s x = n} ∩ f^[n] ⁻¹' t := by
  ext x
  simp [HittingMap]

variable {α : Type*} [MeasureSpace α] {f : α → α} {s : Set α} {μ : Measure α}

lemma _root_.Measurable.hittingMap (hf : Measurable f) (hs : MeasurableSet s) :
    Measurable (HittingMap f s) := by
  intro t ht
  rw [hittingMap_preimage f s t]
  refine MeasurableSet.iUnion fun n ↦ MeasurableSet.inter ?_ (hf.iterate n ht)
  by_cases n₀ : n = 0
  · rw [n₀, hittingTime_zero_set_eq_iInter]
    measurability
  · rw [hittingTime_pos_set_eq_iInter_inter n₀]
    measurability

lemma _root_.Measurable.QuasiMeasurePreserving.hittingMap (hf : QuasiMeasurePreserving f μ μ)
    (hs : MeasurableSet s) :
    QuasiMeasurePreserving (HittingMap f s) μ μ :=
  { measurable := hf.measurable.hittingMap hs
    absolutelyContinuous := by
      refine AbsolutelyContinuous.mk fun t ht t₀ ↦ ?_
      rw [map_apply (hf.measurable.hittingMap hs) ht, hittingMap_preimage f s t]
      refine measure_iUnion_null fun n ↦ ?_
      exact measure_inter_null_of_null_right _ ((hf.iterate n).preimage_null t₀) }

lemma _root_.QuasiMeasurePreserving.aemeasurable_hittingMap (hf : QuasiMeasurePreserving f μ μ)
    (hs : NullMeasurableSet s μ) :
    AEMeasurable (HittingMap f s) μ := by
  obtain ⟨t, s_t, ht, t_μ⟩ := hs.exists_measurable_subset_ae_eq
  refine ⟨HittingMap f t, hf.measurable.hittingMap ht, ?_⟩
  suffices h : HittingTime f s =ᵐ[μ] HittingTime f t by
    refine h.mono fun x hx ↦ ?_
    rw [hittingMap_apply (s := s), hx]
    rfl
  refine EventuallyEq.countable_preimage fun n ↦ ?_
  by_cases n₀ : n = 0
  · rw [n₀, hittingTime_zero_set_eq_iInter, hittingTime_zero_set_eq_iInter]
    refine Filter.EventuallyEq.countable_iInter fun n ↦ ?_
    exact Filter.EventuallyEq.countable_iInter fun _ ↦ (hf.iterate n).preimage_ae_eq t_μ.compl.symm
  · rw [hittingTime_pos_set_eq_iInter_inter n₀, hittingTime_pos_set_eq_iInter_inter n₀]
    refine Filter.EventuallyEq.inter ?_ ((hf.iterate n).preimage_ae_eq t_μ.symm)
    refine Filter.EventuallyEq.countable_iInter fun k ↦ ?_
    exact Filter.EventuallyEq.countable_iInter fun _ ↦ (hf.iterate k).preimage_ae_eq t_μ.compl.symm

open scoped ENNReal

lemma test (u v w : α → ℝ≥0∞) (hf : MeasurePreserving f μ μ)
    (hu : ∀ (z : α → ℝ≥0∞), ∫⁻ x, (u x) * (z (f x)) ∂μ = ∫⁻ x, (v x) * (z x) ∂μ) :
    1 = 1 := by
  sorry

end Recurrence
