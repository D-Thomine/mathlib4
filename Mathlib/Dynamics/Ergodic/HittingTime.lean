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

open EventuallyEq Filter Measurable MeasurableSet MeasureTheory Nat Set

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

lemma hitTime_eq_pos_iff (f : α → α) (s : Set α) (x : α) {n : ℕ} (h₀ : n ≠ 0) :
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
    {x | HitTime f s x = 0} = ⋂ k ≠ 0, f^[k] ⁻¹' sᶜ := by
  ext x
  simp [hitTime_eq_zero_iff_forall]

lemma hitTime_pos_set_eq_iInter_inter {n : ℕ} (h : n ≠ 0) :
    {x | HitTime f s x = n} = (⋂ k ∈ Ioo 0 n, f^[k] ⁻¹' sᶜ) ∩ f^[n] ⁻¹' s := by
  ext x
  simp [hitTime_eq_pos_iff f s x h]

lemma hitTime_image_eq_zero (h : HitTime f s x = 0) :
    HitTime f s (f x) = 0 := by
  refine hitTime_eq_zero_iff_forall.2 fun n n₀ ↦ ?_
  rw [← Function.iterate_succ_apply]
  exact hitTime_eq_zero_iff_forall.1 h n.succ n.succ_ne_zero

lemma mapsTo_hitTime_zero :
    MapsTo f { x | HitTime f s x = 0 } { x | HitTime f s x = 0 } :=
  fun _ h ↦ hitTime_image_eq_zero h

lemma hitTime_ne_zero_of_hitTime_image (h : HitTime f s (f x) ≠ 0) :
    HitTime f s x ≠ 0 :=
  fun h₀ ↦ h (hitTime_image_eq_zero h₀)

lemma hitTime_image_ne_zero (h : HitTime f s x ≠ 0) (hx : f x ∉ s) :
    HitTime f s (f x) ≠ 0 := by
  rw [hitTime_pos_iff_exists]
  refine ⟨HitTime f s x - 1, fun xs ↦ ?_, ?_⟩
  · rw [Nat.sub_eq_zero_iff_le, Nat.le_one_iff_eq_zero_or_eq_one] at xs
    rcases xs with xs | xs
    · exact h xs
    · apply hx
      rw [← Function.iterate_one f, ← xs]
      exact mem_iterate_of_hitTime h
  · rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_one_add_one h]
    exact mem_iterate_of_hitTime h

lemma hitTime_eq_hitTime_image_add_one (h : HitTime f s x ≠ 0) (hx : f x ∉ s) :
    HitTime f s x = HitTime f s (f x) + 1 := by
  rw [hitTime_eq_pos_iff f s x ((HitTime f s (f x)).add_one_ne_zero)]
  simp only [mem_Ioo, and_imp, Function.iterate_succ_apply]
  constructor
  · intro k k₀ kx
    by_cases k₁ : k = 1
    · rwa [k₁, Function.iterate_one]
    have key := ((hitTime_eq_pos_iff f s (f x) (hitTime_image_ne_zero h hx)).1 (by rfl)).1 (k - 1)
    rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_one_add_one k₀.ne.symm] at key
    apply key
    grind
  · exact mem_iterate_of_hitTime (hitTime_image_ne_zero h hx)

lemma hitTime_one_eq_preimage :
    {x | HitTime f s x = 1} = f ⁻¹' s := by
  ext x
  simp only [mem_setOf_eq, hitTime_eq_pos_iff f s x one_ne_zero, mem_Ioo, Function.iterate_one,
    mem_preimage, and_iff_right_iff_imp]
  exact fun _ _ _ _ ↦ by linarith

lemma hitTime_eq_preimage_inter_compl {n : ℕ} (n₀ : n ≠ 0) :
    {x | HitTime f s x = n + 1} = f ⁻¹' ({x | HitTime f s x = n} ∩ sᶜ) := by
  ext x
  simp only [mem_setOf_eq, preimage_inter, preimage_setOf_eq, preimage_compl, mem_inter_iff,
    mem_compl_iff, mem_preimage]
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ ?_⟩
  · apply Nat.add_right_cancel (m := 1)
    rw [← h]
    refine (hitTime_eq_hitTime_image_add_one (by rw [h]; positivity) (fun hx ↦ ?_)).symm
    have : HitTime f s x = 1 := by
      rwa [← Set.mem_setOf_eq (p := fun y ↦ HitTime f s y = 1), hitTime_one_eq_preimage]
    grind
  · rw [← Function.iterate_one f]
    apply ((hitTime_eq_pos_iff f s x n.add_one_ne_zero).1 h).1 1
    simp [Nat.zero_lt_of_ne_zero n₀]
  · rw [← h.1] at n₀ ⊢
    exact hitTime_eq_hitTime_image_add_one (hitTime_ne_zero_of_hitTime_image n₀) h.2

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
  refine .iUnion fun n ↦ .inter ?_ (hf.iterate n ht)
  apply ((hf.hitTime hs) (t := {n}) (by measurability)).congr
  rw [← setOf_eq_eq_singleton, preimage_setOf_eq]

lemma _root_.MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable_hitTime
    (hf : QuasiMeasurePreserving f μ μ) (hs : NullMeasurableSet s μ) :
    AEMeasurable (HitTime f s) μ := by
  obtain ⟨t, s_t, ht, t_μ⟩ := hs.exists_measurable_subset_ae_eq
  refine ⟨HitTime f t, hf.measurable.hitTime ht, .iff_eventuallyEq_preimage.2 fun n ↦ ?_⟩
  by_cases n₀ : n = 0
  · rw [n₀, hitTime_zero_set_eq_iInter, hitTime_zero_set_eq_iInter]
    refine .countable_iInter fun n ↦ .countable_iInter fun _ ↦ ?_
    exact (hf.iterate n).preimage_ae_eq t_μ.compl.symm
  · rw [hitTime_pos_set_eq_iInter_inter n₀, hitTime_pos_set_eq_iInter_inter n₀]
    refine .inter ?_ ((hf.iterate n).preimage_ae_eq t_μ.symm)
    refine .countable_iInter fun k ↦ .countable_iInter fun _ ↦ ?_
    exact (hf.iterate k).preimage_ae_eq t_μ.compl.symm

lemma _root_.MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable_hitMap
    (hf : QuasiMeasurePreserving f μ μ) (hs : NullMeasurableSet s μ) :
    AEMeasurable (HitMap f s) μ := by
  obtain ⟨g, hg, f_g⟩ := hf.aemeasurable_hitTime hs
  refine ⟨fun x ↦ f^[g x] x, fun t ht ↦ ?_, f_g.mono fun x h ↦ ?_⟩
  · refine .congr (s := ⋃ n, { x | g x = n } ∩ f^[n] ⁻¹' t) ?_ (by ext x; simp)
    exact .iUnion fun n ↦ .inter (by measurability) (by measurability)
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

/-- Put this lemma somewhere else. -/
lemma lintegral_indicator_mul_right {t : Set α} (ht : MeasurableSet t) (f g : α → ℝ≥0∞) :
    ∫⁻ x in t, (f x) * (g x) ∂μ = ∫⁻ x, (f x) * (t.indicator g x) ∂μ := by
  rw [← lintegral_indicator ht]; congr 1; ext x
  exact indicator_mul_right t f g

lemma test (u v w : α → ℝ≥0∞) (hf : MeasurePreserving f μ μ) (hs : MeasurableSet s)
    (hu : ∀ (z : α → ℝ≥0∞), ∫⁻ x, (u x) * (z x) ∂μ = ∫⁻ x, (v x) * (z x) ∂μ
      + ∫⁻ x, (u x) * (z (f x)) ∂μ) :
    ∫⁻ x in s, (u x) * (w x) ∂μ = ∫⁻ x in s, (v x) * (w x) ∂μ
      + ∫⁻ x in {y | HitTime f s y = 1} ∩ s, (u x) * (w (f x)) ∂μ
      + ∫⁻ x in {y | HitTime f s y = 1} ∩ sᶜ, (u x) * (w (f x)) ∂μ := by
  rw [lintegral_indicator_mul_right hs u w, hu (s.indicator w),
    ← lintegral_indicator_mul_right hs v w, add_assoc]
  congr 1
  simp only [← indicator_comp_right, ← lintegral_indicator_mul_right (hf.measurable hs) u (w ∘ f),
    hitTime_one_eq_preimage]
  rw [← lintegral_union]
  · simp
  · exact .inter (hf.measurable hs) (by measurability)
  · exact (Disjoint.mono inter_subset_right inter_subset_right) disjoint_compl_right

end Recurrence
