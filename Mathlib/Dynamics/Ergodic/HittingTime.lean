/-
Copyright (c) 2026 Dalien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Dynamics.Ergodic.Conservative

/-!
#

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

lemma hitTime_one_eq_preimage :
    {x | HitTime f s x = 1} = f ⁻¹' s := by
  ext x
  simp only [mem_setOf_eq, hitTime_eq_pos_iff f s x one_ne_zero, mem_Ioo, Function.iterate_one,
    mem_preimage, and_iff_right_iff_imp]
  exact fun _ _ _ _ ↦ by linarith

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

private lemma lintegral_indicator_mul_right {t : Set α} (ht : MeasurableSet t) (f g : α → ℝ≥0∞) :
    ∫⁻ x in t, (f x) * g x ∂μ = ∫⁻ x, (f x) * t.indicator g x ∂μ := by
  rw [← lintegral_indicator ht]; congr 1; ext x
  exact indicator_mul_right t f g

private lemma _root_.Measurable.hitTime_inter {t : Set α} (hf : Measurable f) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (m : ℕ) :
    MeasurableSet ({ y | HitTime f s y = m } ∩ t) := by
  apply MeasurableSet.inter _ ht
  change MeasurableSet ((HitTime f s) ⁻¹' {m})
  exact hf.hitTime hs (by measurability)

private lemma _root_.Measurable.lintegral_hitMap_eq_iterate {t : Set α} {u v : α → ℝ≥0∞}
    (hf : Measurable f) (hs : MeasurableSet s) (ht : MeasurableSet t) (m : ℕ) :
    ∫⁻ (x : α) in {y | HitTime f s y = m} ∩ t, u x * v (HitMap f s x) ∂μ
    = ∫⁻ (x : α) in {y | HitTime f s y = m} ∩ t, u x * v (f^[m] x) ∂μ := by
  refine setLIntegral_congr_fun (hf.hitTime_inter hs ht m) fun x hx ↦ ?_
  rw [HitMap, hx.1]

/-- Works well, but the only reasonnable function on which to use it is u = 1 and v = 0.
Overkill? -/
lemma test (u v w : α → ℝ≥0∞) (hf : Measurable f) (hs : MeasurableSet s) (hw : Measurable w)
    (hu : ∀ {z : α → ℝ≥0∞} (_ : Measurable z), ∫⁻ x, (u x) * z x ∂μ = ∫⁻ x, (v x) * z x ∂μ
      + ∫⁻ x, (u x) * z (f x) ∂μ) {n : ℕ} (n₀ : n ≠ 0) :
    ∫⁻ x in s, (u x) * w x ∂μ = ∫⁻ x in s, (v x) * w x ∂μ
      + ∫⁻ x in {y | HitTime f s y ∈ Ioc 0 n} ∩ s, (u x) * w (HitMap f s x) ∂μ
      + ∫⁻ x in {y | HitTime f s y ∈ Ioo 0 n} ∩ sᶜ, (v x) * w (HitMap f s x) ∂μ
      + ∫⁻ x in {y | HitTime f s y = n} ∩ sᶜ, (u x) * w (HitMap f s x) ∂μ := by
  induction n, (Nat.one_le_iff_ne_zero.2 n₀) using Nat.le_induction with
  | base =>
    -- Simplify the expression.
    have th₁ (m : ℕ) : m ∈ Ioc (0 : ℕ) 1 ↔ m = 1 := by grind only [= mem_Ioc]
    have th₂ (m : ℕ) : m ∈ Ioo (0 : ℕ) 1 ↔ False := by grind only [= mem_Ioo]
    simp only [th₂, setOf_false, empty_inter, setLIntegral_empty, add_zero, th₁,
      hf.lintegral_hitMap_eq_iterate hs hs.compl 1]
    rw [lintegral_indicator_mul_right hs u w, hu (hw.indicator hs),
      ← lintegral_indicator_mul_right hs v w, add_assoc]; clear hu th₁ th₂ n₀ n
    congr 1
    -- Use hu.
    simp only [← indicator_comp_right]
    rw [← lintegral_indicator_mul_right (hf hs) u (w ∘ f), ← hitTime_one_eq_preimage,
      hf.lintegral_hitMap_eq_iterate hs hs 1]
    simp only [Function.comp_apply, Function.iterate_one]
    rw [← lintegral_union (hf.hitTime_inter hs hs.compl 1)]
    · rw [inter_union_compl]
    · exact (Disjoint.mono inter_subset_right inter_subset_right) disjoint_compl_right
  | succ m hm hnm =>
    -- Implement the induction hypothesis and simplify the first term.
    rw [hnm (Nat.one_le_iff_ne_zero.1 hm), add_assoc, add_assoc, add_assoc, add_assoc]; clear n₀ hnm
    congr 1
    -- Split Ioc 0 (m + 1) as Ioc 0 m ∪ {m + 1}, and simplify the Ioc 0 m term.
    have : { y | HitTime f s y ∈ Ioc 0 (m + 1) } ∩ s
      = ({ y | HitTime f s y ∈ Ioc 0 m } ∩ s) ∪ { y | HitTime f s y = m + 1 } ∩ s := by
      ext x
      simp only [mem_Ioc, mem_inter_iff, mem_setOf_eq, mem_union]
      grind only
    rw [this, lintegral_union (hf.hitTime_inter hs hs (m + 1)) (by grind), add_assoc]; clear this
    congr 1
    -- Split Ioo 0 (m + 1) as Ioo 0 m ∪ {m}, and simplify the Ioo 0 m term.
    have : { y | HitTime f s y ∈ Ioo 0 (m + 1) } ∩ sᶜ
      = ({ y | HitTime f s y ∈ Ioo 0 m } ∩ sᶜ) ∪ { y | HitTime f s y = m } ∩ sᶜ := by
      ext x
      simp only [mem_Ioo, Order.lt_add_one_iff, mem_inter_iff, mem_setOf_eq, mem_compl_iff,
        mem_union]
      grind only
    rw [this, lintegral_union (hf.hitTime_inter hs hs.compl m) (by grind)]; clear this
    nth_rw 2 [add_comm]; rw [add_assoc, add_assoc]
    congr 1
    -- Merge the two integrals of u * w ∘ HitMap f s over disjoint sets.
    rw [← lintegral_union (hf.hitTime_inter hs hs (m + 1)) (by grind), union_comm,
      inter_union_compl, hf.lintegral_hitMap_eq_iterate hs hs.compl m,
      ← inter_univ { y | HitTime f s y = m + 1 }, hf.lintegral_hitMap_eq_iterate hs .univ (m + 1),
      inter_univ]
    -- We can at last use hu.
    rw [lintegral_indicator_mul_right (hf.hitTime_inter hs hs.compl m), hu _,
      ← lintegral_indicator_mul_right (hf.hitTime_inter hs hs.compl m)]; swap
    · exact (hw.comp (hf.iterate m)).indicator (hf.hitTime_inter hs hs.compl m)
    simp only [Function.iterate_succ, Function.comp_apply, ← indicator_comp_right]
    rw [← lintegral_indicator_mul_right]; swap
    · apply MeasurableSet.inter _ (hf hs).compl
      change MeasurableSet (((HitTime f s) ∘ f) ⁻¹' {m})
      exact (hf.hitTime hs).comp hf (by measurability)
    rw [← hitTime_eq_preimage_inter_compl (by positivity)]
    simp only [Function.comp_apply, ← Function.iterate_succ_apply, Nat.succ_eq_add_one]
    congr 1
    apply setLIntegral_congr_fun (hf.hitTime_inter hs hs.compl m) fun x hx ↦ ?_
    congr 3
    exact hx.1.symm

/-- Simpler version. -/
lemma test₀ (w : α → ℝ≥0∞) (hf : MeasurePreserving f μ μ) (hs : MeasurableSet s) (hw : Measurable w)
    {n : ℕ} (n₀ : n ≠ 0) :
    ∫⁻ x in s, w x ∂μ = ∫⁻ x in {y | HitTime f s y ∈ Ioc 0 n} ∩ s, w (HitMap f s x) ∂μ
      + ∫⁻ x in {y | HitTime f s y = n} ∩ sᶜ, w (HitMap f s x) ∂μ := by
  induction n, (Nat.one_le_iff_ne_zero.2 n₀) using Nat.le_induction with
  | base =>
    have th₁ (m : ℕ) : m ∈ Ioc (0 : ℕ) 1 ↔ m = 1 := by grind only [= mem_Ioc]
    simp only [th₁]
    rw [← lintegral_union (hf.measurable.hitTime_inter hs hs.compl 1) (by grind), inter_union_compl,
      ← hf.setLIntegral_comp_preimage hs hw, ← hitTime_one_eq_preimage]
    apply setLIntegral_congr_fun
    · change MeasurableSet ((HitTime f s) ⁻¹' {1})
      exact (hf.measurable.hitTime hs) (by measurability)
    · intro x hx
      rw [mem_setOf_eq] at hx
      simp [HitMap, hx]
  | succ m hm hnm =>
    -- Implement the induction hypothesis and simplify the first term.
    rw [hnm (Nat.one_le_iff_ne_zero.1 hm)]; clear n₀ hnm
    -- Split Ioc 0 (m + 1) as Ioc 0 m ∪ {m + 1}, and simplify the Ioc 0 m term.
    have : { y | HitTime f s y ∈ Ioc 0 (m + 1) } ∩ s
      = ({ y | HitTime f s y ∈ Ioc 0 m } ∩ s) ∪ { y | HitTime f s y = m + 1 } ∩ s := by
      ext x
      simp only [mem_Ioc, mem_inter_iff, mem_setOf_eq, mem_union]
      grind only
    rw [this, lintegral_union (hf.measurable.hitTime_inter hs hs (m + 1)) (by grind), add_assoc]
    congr 1; clear this
    -- Merge the two integrals of u * w ∘ HitMap f s over disjoint sets.
    rw [← lintegral_union (hf.measurable.hitTime_inter hs hs.compl (m + 1)) (by grind),
      inter_union_compl]
    have : ∫⁻ (x : α) in { y | HitTime f s y = m } ∩ sᶜ, w (HitMap f s x) ∂μ
      = ∫⁻ (x : α) in { y | HitTime f s y = m } ∩ sᶜ, w (f^[m] x) ∂μ := by
      refine setLIntegral_congr_fun (hf.measurable.hitTime_inter hs hs.compl m) fun x hx ↦ ?_
      rw [HitMap]; congr 2; exact hx.1
    rw [this]; clear this
    have : ∫⁻ (x : α) in { y | HitTime f s y = m + 1 }, w (HitMap f s x) ∂μ
      = ∫⁻ (x : α) in { y | HitTime f s y = m + 1 }, w (f^[m + 1] x) ∂μ := by
      apply setLIntegral_congr_fun
      · change MeasurableSet ((HitTime f s) ⁻¹' {m + 1})
        exact hf.measurable.hitTime hs (by measurability)
      · intro x hx
        simp only [HitMap]; congr 2
    rw [this, ← hf.setLIntegral_comp_preimage (hf.measurable.hitTime_inter hs hs.compl m)]
    · rw [hitTime_eq_preimage_inter_compl (by positivity)]
      rfl
    · exact hw.comp (hf.measurable.iterate m)


lemma test' (u v w : α → ℝ≥0∞) (hf : Measurable f) (hs : MeasurableSet s) (hw : Measurable w)
    (hu : ∀ {z : α → ℝ≥0∞} (_ : Measurable z), ∫⁻ x, (u x) * z x ∂μ = ∫⁻ x, (v x) * z x ∂μ
      + ∫⁻ x, (u x) * z (f x) ∂μ) (hv : EqOn v 0 sᶜ) {n : ℕ} (n₀ : n ≠ 0) :
    ∫⁻ x in s, (u x) * w x ∂μ = ∫⁻ x in s, (v x) * w x ∂μ
      + ∫⁻ x in {y | HitTime f s y ∈ Ioc 0 n} ∩ s, (u x) * w (HitMap f s x) ∂μ
      + ∫⁻ x in {y | HitTime f s y = n} ∩ sᶜ, (u x) * w (HitMap f s x) ∂μ := by
  rw [test u v w hf hs hw hu n₀]
  suffices h : ∫⁻ x in {y | HitTime f s y ∈ Ioo 0 n} ∩ sᶜ, (v x) * w (HitMap f s x) ∂μ = 0 by
    rw [h, add_zero]
  apply setLIntegral_eq_zero
  · apply MeasurableSet.inter _ hs.compl
    change MeasurableSet ((HitTime f s) ⁻¹' (Ioo 0 n))
    exact hf.hitTime hs (by measurability)
  · intro x hx
    simp only [Pi.zero_apply, _root_.mul_eq_zero]
    exact Or.inl (hv hx.2)

lemma test_cor₁ (w : α → ℝ≥0∞) (hf : MeasurePreserving f μ μ) (hs : MeasurableSet s)
    (hw : Measurable w) {n : ℕ} (n₀ : n ≠ 0) :
    ∫⁻ x in s, w x ∂μ = ∫⁻ x in {y | HitTime f s y ∈ Ioc 0 n} ∩ s, w (HitMap f s x) ∂μ
      + ∫⁻ x in {y | HitTime f s y = n} ∩ sᶜ, w (HitMap f s x) ∂μ := by
  have h := test' (μ := μ) 1 0 w hf.measurable hs hw
  simp only [Pi.one_apply, one_mul, Pi.zero_apply, zero_mul, lintegral_const, zero_add,
    eqOn_refl 0 sᶜ, MeasurableSet.univ, Measure.restrict_apply, univ_inter, forall_const] at h
  exact h (fun hz ↦ (hf.lintegral_comp hz).symm) n₀

lemma test_cor₂ (hf : MeasurePreserving f μ μ) (hs : MeasurableSet s) {n : ℕ} (n₀ : n ≠ 0) :
    μ s = μ ({y | HitTime f s y ∈ Ioc 0 n} ∩ s) + μ ({y | HitTime f s y = n} ∩ sᶜ) := by
  have h := test_cor₁ 1 hf hs measurable_one n₀
  simp only [Pi.one_apply, lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter,
    one_mul] at h
  exact h

def ExcursionSum (f : α → α) (s : Set α) (g : α → ℝ≥0∞) :=
  fun x ↦ ∑ n ∈ Finset.Ico 0 (HitTime f s x), g (f^[n] x)

omit [MeasureSpace α] in
lemma excursionSum₁ (g : α → ℝ≥0∞) {x : α} (h : HitTime f s x ≠ 0) (hx : f x ∉ s) :
    ExcursionSum f s g x = ExcursionSum f s g (f x) + g x := by
  rw [ExcursionSum, ExcursionSum, hitTime_eq_hitTime_image_add_one h hx,
    ← Finset.Ico_union_Ico_eq_Ico (b := 1) zero_le (by linarith), Finset.sum_union]; swap
  · refine Finset.disjoint_left.2 fun x hx₁ hx₂ ↦ ?_
    simp only [Ico_succ_singleton, Finset.mem_singleton, Finset.mem_Ico] at hx₁ hx₂
    rw [hx₁] at hx₂
    aesop
  rw [← Finset.sum_Ico_add _ 0 (HitTime f s (f x)) 1, add_comm]
  congr 2
  · ext n
    rw [add_comm, Function.iterate_succ, Function.comp_apply]
  · simp





end Recurrence
