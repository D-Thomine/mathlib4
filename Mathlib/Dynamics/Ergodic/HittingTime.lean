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

open EventuallyEq Filter Function Measurable MeasurableSet MeasureTheory Nat Set

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

lemma hitTime_preimage_zero :
    HitTime f s ⁻¹' {0} = ⋂ k ≠ 0, f^[k] ⁻¹' sᶜ := by
  ext x
  simp [hitTime_eq_zero_iff_forall]

lemma hitTime_preimage_one :
    HitTime f s ⁻¹' {1} = f ⁻¹' s := by
  ext x
  simp only [mem_preimage, mem_singleton_iff, hitTime_eq_pos_iff f s x one_ne_zero, mem_Ioo,
    Order.lt_one_iff, and_imp, iterate_one, and_iff_right_iff_imp]
  exact fun _ _ _ _ ↦ by linarith

lemma hitTime_preimage_of_pos {n : ℕ} (h : n ≠ 0) :
    HitTime f s ⁻¹' {n} = (⋂ k ∈ Ioo 0 n, f^[k] ⁻¹' sᶜ) ∩ f^[n] ⁻¹' s := by
  ext x
  simp [hitTime_eq_pos_iff f s x h]

lemma hitTime_preimage_of_nonzero :
    HitTime f s ⁻¹' Ioi 0 = ⋃ n ≠ 0, f^[n] ⁻¹' s := by
  ext x
  simp only [mem_preimage, mem_Ioi, mem_iUnion, exists_prop, pos_iff_ne_zero,
    hitTime_pos_iff_exists]

lemma hitTime_comp_eq_zero (h : HitTime f s x = 0) :
    HitTime f s (f x) = 0 := by
  refine hitTime_eq_zero_iff_forall.2 fun n n₀ ↦ ?_
  rw [← iterate_succ_apply]
  exact hitTime_eq_zero_iff_forall.1 h n.succ n.succ_ne_zero

lemma mapsTo_hitTime_zero :
    MapsTo f (HitTime f s ⁻¹' {0}) ((HitTime f s) ⁻¹' {0}) :=
  fun _ h ↦ hitTime_comp_eq_zero h

lemma hitTime_ne_zero_of_hitTime_image (h : HitTime f s (f x) ≠ 0) :
    HitTime f s x ≠ 0 :=
  fun h₀ ↦ h (hitTime_comp_eq_zero h₀)

lemma hitTime_image_ne_zero (h : HitTime f s x ≠ 0) (hx : f x ∉ s) :
    HitTime f s (f x) ≠ 0 := by
  rw [hitTime_pos_iff_exists]
  refine ⟨HitTime f s x - 1, fun xs ↦ ?_, ?_⟩
  · rw [Nat.sub_eq_zero_iff_le, Nat.le_one_iff_eq_zero_or_eq_one] at xs
    rcases xs with xs | xs
    · exact h xs
    · apply hx
      rw [← iterate_one f, ← xs]
      exact mem_iterate_of_hitTime h
  · rw [← iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_one_add_one h]
    exact mem_iterate_of_hitTime h

lemma hitTime_eq_hitTime_image_add_one (h : HitTime f s x ≠ 0) (hx : f x ∉ s) :
    HitTime f s x = HitTime f s (f x) + 1 := by
  rw [hitTime_eq_pos_iff f s x ((HitTime f s (f x)).add_one_ne_zero)]
  simp only [mem_Ioo, and_imp, iterate_succ_apply]
  constructor
  · intro k k₀ kx
    by_cases k₁ : k = 1
    · rwa [k₁, iterate_one]
    have key := ((hitTime_eq_pos_iff f s (f x) (hitTime_image_ne_zero h hx)).1 (by rfl)).1 (k - 1)
    rw [← iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_one_add_one k₀.ne.symm] at key
    apply key
    grind
  · exact mem_iterate_of_hitTime (hitTime_image_ne_zero h hx)

lemma hitTime_eq_preimage_inter_compl {n : ℕ} (n₀ : n ≠ 0) :
    HitTime f s ⁻¹' {n + 1} = f ⁻¹' ((HitTime f s ⁻¹' {n}) ∩ sᶜ) := by
  ext x
  simp only [mem_preimage, mem_singleton_iff, preimage_inter, preimage_compl, mem_inter_iff,
    mem_compl_iff]
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ ?_⟩
  · apply Nat.add_right_cancel (m := 1)
    rw [← h]
    refine (hitTime_eq_hitTime_image_add_one (by rw [h]; positivity) (fun hx ↦ ?_)).symm
    have : HitTime f s x = 1 := by
      rwa [← mem_preimage, ← hitTime_preimage_one, mem_preimage, mem_singleton_iff] at hx
    grind
  · rw [← iterate_one f]
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
  hitMap_mem_iff.2 (.inl h)

lemma mapsTo_hitMap (f : α → α) (s : Set α) :
    MapsTo (HitMap f s) s s :=
  fun _ h ↦ hitMap_mem_iff.2 (.inr h)

lemma hitMap_preimage (f : α → α) (s t : Set α) :
    (HitMap f s) ⁻¹' t = ⋃ n, {x | HitTime f s x = n} ∩ f^[n] ⁻¹' t := by
  ext x
  simp [HitMap]

variable {α : Type*} [MeasureSpace α] {f : α → α} {s : Set α} {μ : Measure α}

@[fun_prop]
lemma _root_.Measurable.hitTime (hf : Measurable f) (hs : MeasurableSet s) :
    Measurable (HitTime f s) := by
  refine measurable_to_countable' fun n ↦ ?_
  by_cases n₀ : n = 0
  · rw [n₀, hitTime_preimage_zero]; measurability
  · rw [hitTime_preimage_of_pos n₀]; measurability

@[fun_prop]
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
  · rw [n₀, hitTime_preimage_zero, hitTime_preimage_zero]
    refine .countable_iInter fun n ↦ .countable_iInter fun _ ↦ ?_
    exact (hf.iterate n).preimage_ae_eq t_μ.compl.symm
  · rw [hitTime_preimage_of_pos n₀, hitTime_preimage_of_pos n₀]
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

lemma _root_.MeasureTheory.MeasurePreserving.lintegral_eq_lintegral_comp_hitMap_add (w : α → ℝ≥0∞)
    {n : ℕ} (hf : MeasurePreserving f μ μ) (hs : MeasurableSet s) (hw : Measurable w) (n₀ : n ≠ 0) :
    ∫⁻ x in s, w x ∂μ = ∫⁻ x in HitTime f s ⁻¹' Ioc 0 n ∩ s, w (HitMap f s x) ∂μ
      + ∫⁻ x in HitTime f s ⁻¹' {n} ∩ sᶜ, w (HitMap f s x) ∂μ := by
  induction n, (Nat.one_le_iff_ne_zero.2 n₀) using Nat.le_induction with
  | base =>
    have : Ioc (0 : ℕ) 1 = {1} := by grind only [= mem_Ioc, = mem_singleton_iff]
    simp only [this]; clear this
    rw [← lintegral_union (((hf.measurable.hitTime hs) (singleton 1)).inter hs.compl) (by grind),
      inter_union_compl, ← hf.setLIntegral_comp_preimage hs hw, ← hitTime_preimage_one]
    refine setLIntegral_congr_fun ((hf.measurable.hitTime hs) (singleton 1)) fun x hx ↦ ?_
    rw [mem_preimage, mem_singleton_iff] at hx
    rw [HitMap, hx, iterate_one]
  | succ m hm hnm =>
    -- Implement the induction hypothesis and simplify the first term.
    rw [hnm (Nat.one_le_iff_ne_zero.1 hm)]; clear n₀ hnm
    -- Split Ioc 0 (m + 1) as Ioc 0 m ∪ {m + 1}, and simplify the Ioc 0 m term.
    have : HitTime f s ⁻¹' Ioc 0 (m + 1) ∩ s
      = (HitTime f s ⁻¹' Ioc 0 m ∩ s) ∪ HitTime f s ⁻¹' {m + 1} ∩ s := by
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_Ioc, mem_union, mem_singleton_iff]
      grind only
    rw [this, lintegral_union (((hf.measurable.hitTime hs) (singleton (m + 1))).inter hs)
      (by grind), add_assoc]
    congr 1; clear this
    -- Merge the two integrals of u * w ∘ HitMap f s over disjoint sets.
    rw [← lintegral_union (((hf.measurable.hitTime hs) (singleton (m + 1))).inter hs.compl)
      (by grind), inter_union_compl]
    have : ∫⁻ (x : α) in HitTime f s ⁻¹' {m} ∩ sᶜ, w (HitMap f s x) ∂μ
      = ∫⁻ (x : α) in HitTime f s ⁻¹' {m} ∩ sᶜ, w (f^[m] x) ∂μ := by
      apply setLIntegral_congr_fun ((((hf.measurable.hitTime hs) (singleton m))).inter hs.compl)
      intro x hx
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff] at hx
      simp only [HitMap, hx.1]
    rw [this]; clear this
    have : ∫⁻ (x : α) in HitTime f s ⁻¹' {m + 1}, w (HitMap f s x) ∂μ
      = ∫⁻ (x : α) in HitTime f s ⁻¹' {m + 1}, w (f^[m + 1] x) ∂μ := by
      apply setLIntegral_congr_fun (hf.measurable.hitTime hs (singleton (m + 1)))
      intro x hx
      simp only [mem_preimage, mem_singleton_iff] at hx
      simp only [HitMap, hx]
    rw [this, ← hf.setLIntegral_comp_preimage
      ((((hf.measurable.hitTime hs) (singleton m))).inter hs.compl) _]
    · rw [hitTime_eq_preimage_inter_compl (by positivity)]
      rfl
    · exact hw.comp (hf.measurable.iterate m)

lemma _root_.MeasureTheory.MeasurePreserving.measure_hitTime_preimage_add {n : ℕ}
    (hf : MeasurePreserving f μ μ) (hs : MeasurableSet s) (n₀ : n ≠ 0) :
    μ s = μ (HitTime f s ⁻¹' Ioc 0 n ∩ s) + μ (HitTime f s ⁻¹' {n} ∩ sᶜ) := by
  have h := hf.lintegral_eq_lintegral_comp_hitMap_add 1 hs measurable_one n₀
  simp only [Pi.one_apply, lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter,
    one_mul] at h
  exact h

lemma _root_.MeasureTheory.MeasurePreserving.tendsto_measure_hitTime_zero
    (hf : MeasurePreserving f μ μ) (hs : MeasurableSet s) (hsr : IsRecurrent f μ s)
    (hsμ : μ s ≠ ⊤) :
    Tendsto (fun n ↦ μ (HitTime f s ⁻¹' {n} ∩ sᶜ)) atTop (nhds 0) := by
  apply Tendsto.congr' (f₁ := fun n ↦ μ s -  μ (HitTime f s ⁻¹' Ioc 0 n ∩ s))
  · refine eventually_atTop.2 ⟨1, fun n n₁ ↦ ?_⟩
    apply ENNReal.sub_eq_of_eq_add_rev (measure_lt_top_mono inter_subset_right hsμ.lt_top).ne
    exact hf.measure_hitTime_preimage_add hs (by linarith)
  rw [← tsub_self (μ s)]
  apply ENNReal.Tendsto.sub tendsto_const_nhds _ (.inl hsμ)
  suffices h : μ s = μ (⋃ n, HitTime f s ⁻¹' Ioc 0 n ∩ s) by
    rw [h]
    refine tendsto_measure_iUnion_atTop fun n m hnm ↦ ?_
    exact inter_subset_inter_left s (preimage_mono (Ioc_subset_Ioc_right hnm))
  rw [← iUnion_inter, ← preimage_iUnion, iUnion_Ioc_right, hitTime_preimage_of_nonzero]
  apply (measure_eq_measure_of_null_sdiff inter_subset_right _).symm
  rw [sdiff_inter_self_eq_sdiff]
  exact ae_le_set.1 (isRecurrent_def.1 hsr)

lemma _root_.MeasureTheory.MeasurePreserving.tendsto_measure_hitTime_zero'
    (hf : MeasurePreserving f μ μ) (hs : MeasurableSet s) (hsr : IsRecurrent f μ s)
    (hsμ : μ s ≠ ⊤) :
    Tendsto (fun n ↦ μ (HitTime f s ⁻¹' {n})) atTop (nhds 0) := by
  have : (fun n ↦ μ (HitTime f s ⁻¹' {n}))
    = (fun n ↦ μ (HitTime f s ⁻¹' {n} ∩ s)) + fun n ↦ μ (HitTime f s ⁻¹' {n} ∩ sᶜ) := by
    ext n
    rw [Pi.add_apply, ← measure_union (by grind)
      ((hf.measurable.hitTime hs (singleton n)).inter hs.compl), inter_union_compl]
  rw [this]; clear this
  sorry

lemma _root_.MeasureTheory.MeasurePreserving.lintegral_eq_lintegral_comp_hitMap (w : α → ℝ≥0∞)
    (hf : MeasurePreserving f μ μ) (hs : MeasurableSet s) (hsr : IsRecurrent f μ s)
    (hsμ : μ s ≠ ⊤) (hw : Measurable w) :
    ∫⁻ x in s, w x ∂μ = ∫⁻ x in s, w (HitMap f s x) ∂μ := by
  apply tendsto_nhds_unique (f := fun n : ℕ ↦ ∫⁻ x in s, w x ∂μ) (l := atTop) tendsto_const_nhds
  apply Tendsto.congr' (f₁ := fun n ↦ ∫⁻ x in HitTime f s ⁻¹' Ioc 0 n ∩ s, w (HitMap f s x) ∂μ
    + ∫⁻ x in HitTime f s ⁻¹' {n} ∩ sᶜ, w (HitMap f s x) ∂μ)
  · refine eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩
    exact (hf.lintegral_eq_lintegral_comp_hitMap_add w hs hw (by linarith)).symm
  sorry
















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
