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

## Implementation notes
The hitting time of a set `s` for a point `x` under a transformation `f` is defined as the `sInf`
of all positive times `n` such that `f^[n] x ∈ s`. By default, `sInf ∅ = 0`. Hence, if the orbit
starting from `x` never returns to `s`, then `HitTime f s x = 0`. This convention differs from the
usual convention on the subject, for which `HitTime f s x = +∞` if the orbit starting from `x`
never returns to `s`. The convention adopted therein has some upsides (e.g. `HitMap` is defined
everywhere, `s` is stable under `HitMap`), but also some limitations one should keep in mind
(e.g. `HitTime f s` is not antitone in `s`).

The version of Kac's formula we implement here is more naturally expressed using transfer operators.
However, in order to avoid implementing or importing the necessary background, we work around by
expliciting the underlying duality. /- Cite sources + quote lemmas-/

## Tags

hitting time, hitting map, induction
-/

public section

noncomputable section

namespace Recurrence

open Filter Measurable MeasureTheory Nat Set

open Measure

variable {α : Type*} {f : α → α} {s : Set α} {x : α}

/-- `HitTime f s` is the function which to each point `x` associates the first positive time `n`
at which the iterate `f^[n] x` belongs to `s`. By the convention `sInf ∅ = 0`, if the positive orbit
of `x` never hits `s`, then `HitTime f s x = 0`. -/
def HitTime (f : α → α) (s : Set α) :=
    fun x ↦ sInf {n : ℕ | n ≠ 0 ∧ f^[n] x ∈ s}

lemma hitTime_eq_zero_iff_forall :
    HitTime f s x = 0 ↔ ∀ n ≠ 0, f^[n] x ∉ s := by
  simp [HitTime, Set.eq_empty_iff_forall_notMem]

lemma hitTime_pos_iff_exists :
    HitTime f s x ≠ 0 ↔ ∃ n ≠ 0, f^[n] x ∈ s := by
  rw [← not_iff_not]
  simp [hitTime_eq_zero_iff_forall]

lemma not_mem_iterate_of_lt_hitTime {n : ℕ} (h₀ : n ≠ 0) (h : n < HitTime f s x) :
    f^[n] x ∉ s :=
  fun hx ↦ notMem_of_lt_sInf h ⟨h₀, hx⟩

lemma mem_iterate_of_hitTime (h : HitTime f s x ≠ 0) :
    f^[HitTime f s x] x ∈ s :=
  (sInf_mem (nonempty_of_pos_sInf (pos_of_ne_zero h))).2

lemma hitTime_eq_pos_iff {n : ℕ} (h₀ : n ≠ 0) :
    HitTime f s x = n ↔ (∀ k ∈ Ioo 0 n, f^[k] x ∉ s) ∧ f^[n] x ∈ s := by
  simp only [mem_Ioo, and_imp]
  constructor <;> intro h
  · rw [← h] at h₀ ⊢
    exact ⟨fun k k₀ kn ↦ not_mem_iterate_of_lt_hitTime k₀.ne.symm kn,
      mem_iterate_of_hitTime h₀⟩
  · refine eq_iff_le_not_lt.2 ⟨Nat.sInf_le ⟨h₀, h.2⟩, fun hn ↦ ?_⟩
    have ht₀ : 0 < HitTime f s x := pos_of_ne_zero (hitTime_pos_iff_exists.2 ⟨n, h₀, h.2⟩)
    exact h.1 (HitTime f s x) ht₀ hn (mem_iterate_of_hitTime ht₀.ne.symm)

lemma hitTime_zero_set_eq_iInter :
    {x | HitTime f s x = 0} = (⋂ k ≠ 0, f^[k] ⁻¹' sᶜ) := by
  ext x
  simp [hitTime_eq_zero_iff_forall]

lemma hitTime_pos_set_eq_iInter_inter {n : ℕ} (h : n ≠ 0) :
    {x | HitTime f s x = n} = (⋂ k ∈ Ioo 0 n, f^[k] ⁻¹' sᶜ) ∩ f^[n] ⁻¹' s := by
  ext x
  simp [hitTime_eq_pos_iff h]

/-- `HitMap f s` is the function which to each point `x` associates the point at which the
positive orbit of `x` first hits `s`. By the convention `sInf ∅ = 0`, if the positive orbit
of `x` never hits `s`, then `HitMap f s x = x`. -/
def HitMap (f : α → α) (s : Set α) :=
    fun x ↦ f^[HitTime f s x] x

lemma hitMap_apply : HitMap f s x = f^[HitTime f s x] x := by rfl

lemma hitMap_eq_self_of_hitTime_zero (h : HitTime f s x = 0) :
    HitMap f s x = x := by
  simp [HitMap, h]

lemma hitMap_mem_iff :
    HitMap f s x ∈ s ↔ HitTime f s x ≠ 0 ∨ x ∈ s := by
  by_cases h : HitTime f s x = 0
  · simp [h, hitMap_eq_self_of_hitTime_zero h]
  · simp only [ne_eq, h, not_false_eq_true, true_or, iff_true]
    exact mem_iterate_of_hitTime h

lemma hitMap_mem_of_hitTime_pos (h : HitTime f s x ≠ 0) :
    HitMap f s x ∈ s :=
  hitMap_mem_iff.2 (Or.inl h)

lemma mapsTo_hitMap (f : α → α) (s : Set α) :
    MapsTo (HitMap f s) s s :=
  fun _ h ↦hitMap_mem_iff.2 (Or.inr h)

lemma hitMap_preimage (f : α → α) (s t : Set α) :
    (HitMap f s) ⁻¹' t = ⋃ n, {x | HitTime f s x = n} ∩ f^[n] ⁻¹' t := by
  ext x
  simp [HitMap]

variable {α : Type*} [MeasureSpace α] {f : α → α} {s : Set α} {μ : Measure α}

lemma _root_.Measurable.hitTime (hf : Measurable f) (hs : MeasurableSet s) :
    Measurable (HitTime f s) := by
  refine measurable_to_countable' fun n ↦ ?_
  by_cases n₀ : n = 0
  · rw [n₀, ← setOf_eq_eq_singleton, preimage_setOf_eq, hitTime_zero_set_eq_iInter]
    measurability
  · rw [← setOf_eq_eq_singleton, preimage_setOf_eq, hitTime_pos_set_eq_iInter_inter n₀]
    measurability

lemma _root_.Measurable.hitMap (hf : Measurable f) (hs : MeasurableSet s) :
    Measurable (HitMap f s) := by
  intro t ht
  rw [hitMap_preimage f s t]
  refine MeasurableSet.iUnion fun n ↦ MeasurableSet.inter ?_ (hf.iterate n ht)
  apply ((hf.hitTime hs) (t := {n}) (by measurability)).congr
  rw [← setOf_eq_eq_singleton, preimage_setOf_eq]

lemma _root_.MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable_hitTime
    (hf : QuasiMeasurePreserving f μ μ) (hs : NullMeasurableSet s μ) :
    AEMeasurable (HitTime f s) μ := by
  obtain ⟨t, s_t, ht, t_μ⟩ := hs.exists_measurable_subset_ae_eq
  refine ⟨HitTime f t, hf.measurable.hitTime ht, EventuallyEq.iff_eventuallyEq_preimage.2 fun n ↦ ?_⟩
  by_cases n₀ : n = 0
  · rw [n₀, hitTime_zero_set_eq_iInter, hitTime_zero_set_eq_iInter]
    refine Filter.EventuallyEq.countable_iInter fun n ↦ ?_
    exact Filter.EventuallyEq.countable_iInter fun _ ↦ (hf.iterate n).preimage_ae_eq t_μ.compl.symm
  · rw [hitTime_pos_set_eq_iInter_inter n₀, hitTime_pos_set_eq_iInter_inter n₀]
    refine Filter.EventuallyEq.inter ?_ ((hf.iterate n).preimage_ae_eq t_μ.symm)
    refine Filter.EventuallyEq.countable_iInter fun k ↦ ?_
    exact Filter.EventuallyEq.countable_iInter fun _ ↦ (hf.iterate k).preimage_ae_eq t_μ.compl.symm

lemma _root_.MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable_hitMap
    (hf : QuasiMeasurePreserving f μ μ) (hs : NullMeasurableSet s μ) :
    AEMeasurable (HitMap f s) μ := by
  obtain ⟨g, hg, f_g⟩ := hf.aemeasurable_hitTime hs
  refine ⟨fun x ↦ f^[g x] x, fun t ht ↦ ?_, f_g.mono fun x h ↦ ?_⟩
  · refine MeasurableSet.congr (s := ⋃ n, { x | g x = n } ∩ f^[n] ⁻¹' t) ?_ (by ext x; simp)
    exact MeasurableSet.iUnion fun n ↦ MeasurableSet.inter (by measurability) (by measurability)
  · rw [HitMap, h]

lemma _root_.Measurable.QuasiMeasurePreserving.hitMap (hf : QuasiMeasurePreserving f μ μ)
    (hs : MeasurableSet s) :
    QuasiMeasurePreserving (HitMap f s) μ μ :=
  { measurable := hf.measurable.hitMap hs
    absolutelyContinuous := by
      refine AbsolutelyContinuous.mk fun t ht t₀ ↦ ?_
      rw [map_apply (hf.measurable.hitMap hs) ht, hitMap_preimage f s t]
      refine measure_iUnion_null fun n ↦ ?_
      exact measure_inter_null_of_null_right _ ((hf.iterate n).preimage_null t₀) }

open scoped ENNReal

lemma test (u v w : α → ℝ≥0∞) (hf : MeasurePreserving f μ μ) (hs : MeasurableSet s)
    (hu : ∀ (z : α → ℝ≥0∞), ∫⁻ x, (u x) * (z x) ∂μ = ∫⁻ x, (v x) * (z x) ∂μ
      + ∫⁻ x, (u x) * (z (f x)) ∂μ) :
    ∫⁻ x in s, (u x) * (w x) ∂μ = ∫⁻ x in s, (v x) * (w x) ∂μ
      + ∫⁻ x in {y | HitTime f s y = 1} ∩ s, (u x) * (w (f x)) ∂μ
      + ∫⁻ x in {y | HitTime f s y = 1} ∩ sᶜ, (u x) * (w (f x)) ∂μ := by
  have h₁ {t : Set α} (ht : MeasurableSet t) (z₁ z₂ : α → ℝ≥0∞) :
    ∫⁻ x in t, (z₁ x) * (z₂ x) ∂μ = ∫⁻ x, (z₁ x) * (t.indicator z₂ x) ∂μ := by
      rw [← lintegral_indicator ht]; congr 1; ext x
      exact indicator_mul_right t z₁ z₂
  rw [h₁ hs u w, hu (s.indicator w), ← h₁ hs v w, add_assoc]
  congr 1
  simp only [← indicator_comp_right, ← h₁ (hf.measurable hs) u (w ∘ f)]
  rw [← lintegral_union]
  · simp only [Function.comp_apply, inter_union_compl]
    congr 2
    rw [hitTime_pos_set_eq_iInter_inter one_ne_zero]
    simp only [mem_Ioo, Order.lt_one_iff, preimage_compl, Function.iterate_one, right_eq_inter,
      subset_iInter_iff, and_imp]
    intro k k₀ k₁
    linarith
  · refine MeasurableSet.inter ?_ (by measurability)
    have : {y | HitTime f s y = 1} = (HitTime f s) ⁻¹' {1} := by
      ext y; simp
    rw [this]
    apply hf.measurable.hitTime hs
    measurability
  · exact (Disjoint.mono inter_subset_right inter_subset_right) disjoint_compl_right

/- TODO :
  Extraire les propriétés de récurrence sur HitTime (du type HitTime f s (f x) = ...), HitMap.
  En déduire une caractérisation récurrente de {HitTime = n}.
  Finir test. -/


end Recurrence
