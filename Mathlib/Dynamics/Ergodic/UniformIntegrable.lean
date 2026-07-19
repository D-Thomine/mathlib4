/-
Copyright (c) 2026 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
module

public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Hitting time and hitting map in measured dynamical systems
In this file, we define first hitting maps in measured dynamical systems.

## Main definitions
- `HitTime`: given a map `f : α → α` and a set `s`, the first positive time at which an iteration of
  `f` hits `s`. Its value is `0` if no iteration hits `s`.
- `HitMap`: given a map `f : α → α` and a set `s`, the point at which an iteration of `f` first hits
  `s`.
- `ExcursionSum` : given a map `f : α → α` a set `s` and an `ℝ≥0∞`-valued function `w` on `α`, the
  sum of `w` on an orbit until this orbit first hits `s`.

## Implementation notes
The hitting time of a set `s` for a point `x` under a transformation `f` is defined as the `sInf`
of all positive times `n` such that `f^[n] x ∈ s`. By default, `sInf ∅ = 0`. Hence, if the orbit
starting from `x` never returns to `s`, then `HitTime f s x = 0`. This convention differs from the
usual convention on the subject, for which `HitTime f s x = +∞` if the orbit starting from `x`
never returns to `s`. The convention adopted therein has some upsides (e.g. `HitMap` is defined
everywhere, `s` is stable under `HitMap`), but also some limitations one should keep in mind
(e.g. `HitTime f s` is not antitone in `s`).

## TODO
Prove:
- That `HitMap f s` is measure-preserving if `f` is measure-preserving and `s` recurrent.
- If possible, remove the hypothesis that `s` has finite measure in the previous theorem.
- Kac's lemma (or rather, its generalization for nonnegative functions): if `f` is
measure-preserving and `s` recurrent, then
`∫⁻ x in (⋃ n, f^[n] ⁻¹' s), w x ∂μ = ∫⁻ x in s, ExcursionSum f s x ∂μ`.

## Tags
hitting time, hitting map, induction, recurrent set
-/

public section

noncomputable section

namespace MeasureTheory

open ENNReal Filter Function Measure Set Topology

@[instance] theorem _root_.ENNReal.NeZero.top : NeZero ∞ := { out := zero_ne_top.symm }

variable {α ι : Type*} [MeasurableSpace α] {F : ι → α → ℝ≥0∞} {μ : Measure α}

/-! ### Uniform integrability -/

def UnifLIntegrable (F : ι → α → ℝ≥0∞) (μ : Measure α) :=
  Tendsto (fun ε ↦ ⨆ (i : ι) (A : Set α) (_ : μ A ≤ ε), ∫⁻ x in A, F i x ∂μ) (𝓝 0) (𝓝 0)

lemma unifLIntegrable_def :
    UnifLIntegrable F μ ↔ Tendsto (fun ε ↦ ⨆ (i : ι) (A : Set α) (_ : μ A ≤ ε),
    ∫⁻ x in A, F i x ∂μ) (𝓝 0) (𝓝 0) := by rfl

lemma unifLIntegrable_mk :
    UnifLIntegrable F μ ↔ Tendsto (fun ε ↦ ⨆ (i : ι) (A : Set α) (_ : MeasurableSet A)
    (_ : μ A ≤ ε), ∫⁻ x in A, F i x ∂μ) (𝓝 0) (𝓝 0) := by
  rw [unifLIntegrable_def, iff_iff_eq]; congr 2; ext ε
  refine iSup_congr fun i ↦ le_antisymm (iSup₂_le fun A hAμ ↦ ?_) (iSup_mono fun A ↦ by simp)
  obtain ⟨B, hAB, hB, hBμ⟩ := exists_measurable_superset μ A
  rw [← hBμ] at hAμ
  apply (le_iSup _ B).trans'
  apply (le_iSup _ hB).trans'
  apply (le_iSup _ hAμ).trans'
  exact lintegral_mono_set hAB

lemma UnifLIntegrable.tendsto_comp_set {A : ι → Set α} {l : Filter ι} (h : UnifLIntegrable F μ)
    (hAμ : Tendsto (μ ∘ A) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫⁻ x in A i, F i x ∂μ) l (𝓝 0) := by
  have key := h.comp hAμ
  rw [← bot_eq_zero] at key ⊢
  refine tendsto_nhds_bot_mono' key (fun i ↦ ?_)
  simp only [comp_apply]
  apply (le_iSup _ i).trans'
  apply (le_iSup _ (A i)).trans'
  simp

lemma tendsto_iSup_setLIntegral_zero {f : α → ℝ≥0∞} (hf : ∫⁻ x, f x ∂μ ≠ ∞) :
    Tendsto (fun ε ↦ ⨆ (A : Set α) (_ : μ A ≤ ε), ∫⁻ x in A, f x ∂μ) (𝓝 0) (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ ?_
  rw [nhds_zero_basis.eventually_iff]
  obtain ⟨δ, hδ, hfδ⟩ := exists_pos_setLIntegral_lt_of_measure_lt hf hε.ne.symm
  refine ⟨δ, hδ, fun a ha ↦ ?_⟩
  simp only [iSup_le_iff]
  grind

/-! ### Equi-integrability -/

def UniformLIntegrable (F : ι → α → ℝ≥0∞) (μ : Measure α) :=
  Tendsto (fun a ↦ ⨆ i, ∫⁻ x in F i ⁻¹' Ici a, F i x ∂μ) (𝓝 ∞) (𝓝 0)

lemma uniformLIntegrable_def :
    UniformLIntegrable F μ
      ↔ Tendsto (fun a ↦ ⨆ i, ∫⁻ x in F i ⁻¹' Ici a, F i x ∂μ) (𝓝 ∞) (𝓝 0) := by rfl

-- Auxiliary lemma to prove that `UniformLIntegrable` families are `UnifLIntegrable`.
private lemma setLIntegral_le_add_lintegral (f : α → ℝ≥0∞) (A : Set α) (a : ℝ≥0∞) :
    ∫⁻ x in A, f x ∂μ ≤ a * μ A + ∫⁻ x in f ⁻¹' Ici a, f x ∂μ := by
  -- Without loss of generality, `A` can be assumed measurable.
  obtain ⟨B, hAB, hB, hBμ⟩ := exists_measurable_superset μ A
  apply (lintegral_mono_set hAB).trans
  rw [← hBμ]; clear hBμ hAB A
  -- We replace `f` by a measurable approximation `g` of `f`.
  obtain ⟨g, hg, hfg, hgμ⟩ := exists_measurable_le_lintegral_eq (μ.restrict B) f
  rw [hgμ]
  apply le_trans (b := a * μ B + ∫⁻ x in g ⁻¹' Ici a, g x ∂μ)
  -- Main argument : on `(g ⁻¹' Ici a)ᶜ`, the function `g` is bounded by `a`.
  · rw [← lintegral_inter_add_sdiff g B (.preimage (measurableSet_Ici (a := a)) hg), add_comm]
    apply add_le_add _ (lintegral_mono_set inter_subset_right)
    rw [← setLIntegral_const]
    apply (setLIntegral_mono (measurable_const (a := a)) (by grind)).trans
    exact lintegral_mono_set sdiff_subset
  -- We finally relate bound `∫⁻ x in g ⁻¹' Ici a, g x ∂μ` with `∫⁻ x in f ⁻¹' Ici a, f x ∂μ`.
  · apply add_le_add_right
    apply le_trans (b := ∫⁻ x in g ⁻¹' Ici a, f x ∂μ)
    · exact setLIntegral_mono' (by measurability) (fun x _ ↦ Pi.le_def.1 hfg x)
    · refine lintegral_mono_set fun x hx ↦ ?_
      simp only [mem_preimage, mem_Ici] at hx ⊢
      exact hx.trans (Pi.le_def.1 hfg x)

lemma UniformLIntegrable.lintegral_lt_top_of_isFinite (hμ : IsFiniteMeasure μ)
    (h : UniformLIntegrable F μ) :
    ⨆ i, ∫⁻ x, F i x ∂μ < ∞ := by
  have key := (ENNReal.tendsto_nhds_zero.1 h 1 zero_lt_one).and_frequently (frequently_lt_nhds ∞)
  obtain ⟨a, ha, a_top⟩ := key.exists
  apply lt_of_le_of_lt (b := a * μ univ + 1)
  · simp only [iSup_le_iff] at ha ⊢
    intro i
    rw [← setLIntegral_univ (F i)]
    apply (setLIntegral_le_add_lintegral (F i) univ a).trans
    exact add_le_add_right (ha i) (a * μ univ)
  · exact add_lt_top.2 ⟨mul_lt_top a_top ((isFiniteMeasure_iff μ).1 hμ), one_lt_top⟩

lemma UniformLIntegrable.unifLIntegrable (h : UniformLIntegrable F μ) : UnifLIntegrable F μ := by
  -- The key is Lemma `setLIntegral_le_add_lintegral`.
  -- Choose `a` large enough that `∫⁻ x in f ⁻¹' Ici a, f x ∂μ` is small.
  -- Then, choose `μ A` small enough that `a * μ A` is also small.
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ nhds_zero_basis.eventually_iff.2 ?_
  obtain ⟨δ, hδ, hδε⟩ := exists_between hε
  obtain ⟨a, ha, haF⟩ :=
    ENNReal.nhds_top_basis.eventually_iff.1 (ENNReal.tendsto_nhds_zero.1 h δ hδ)
  obtain ⟨b, hab, hb⟩ := exists_between ha
  have hδε' : ε - δ ≠ 0 := fun p ↦ hδε.not_ge (tsub_eq_zero_iff_le.1 p)
  obtain ⟨κ, hκ, hκb⟩ := ENNReal.exists_pos_mul_lt hb.ne hδε'
  specialize haF (mem_Ioi.2 hab)
  refine ⟨κ, hκ, fun γ hγ ↦ ?_⟩
  simp only [iSup_le_iff] at haF ⊢
  intro i A hAμ
  apply (setLIntegral_le_add_lintegral (F i) A b).trans
  rw [← tsub_add_cancel_of_le hδε.le, mul_comm (a := b)]
  apply add_le_add (hκb.le.trans' _) (haF i)
  exact mul_le_mul_left (hAμ.trans (mem_Iio.1 hγ).le) b

lemma UnifLIntegrable.uniformLIntegrable_of_lintegral_lt_top (hF : ∀ i, AEMeasurable (F i) μ)
    (h : UnifLIntegrable F μ) (h' : ⨆ i, ∫⁻ x, F i x ∂μ ≠ ∞) :
    UniformLIntegrable F μ := by
  -- Markov's inequality with yields uniform decay of `μ (F i ⁻¹' Ici a)`.
  -- The hypothesis `UnifLIntegrable F μ` implies uniform decay of `∫⁻ x in f ⁻¹' Ici a, f x ∂μ`.
  rw [UniformLIntegrable, ← bot_eq_zero]
  suffices key : Tendsto (fun a ↦ ⨆ i, μ (F i ⁻¹' Ici a)) (𝓝 ∞) (𝓝 ⊥) by
    refine tendsto_nhds_bot_mono' (h.comp key) fun a ↦ ?_
    simp only [comp_apply, iSup_le_iff]
    intro i
    apply (le_iSup _ i).trans'
    apply (le_iSup _ ((F i) ⁻¹' Ici a)).trans'
    rw [iSup_pos]
    exact le_iSup (α := ℝ≥0∞) _ i
  apply tendsto_nhds_bot_mono (f := fun a ↦ (⨆ i, ∫⁻ x, F i x ∂μ) / a)
  · have := Tendsto.const_div (a := ⨆ i, ∫⁻ x, F i x ∂μ) (b := ∞) tendsto_id (.inr h')
    simp only [id_eq, div_top] at this
    rwa [ENNReal.bot_eq_zero]
  · refine (eventually_gt_nhds zero_lt_top).mono fun a ha₀ ↦ ?_
    simp only [ENNReal.iSup_div]
    refine iSup_mono fun i ↦ ?_
    rcases eq_or_ne a ⊤ with rfl | ha
    · simp only [Ici_top, div_top, nonpos_iff_eq_zero]
      exact measure_eq_top_of_lintegral_ne_top (hF i) ((le_iSup _ i).trans_lt h'.lt_top).ne
    · exact meas_ge_le_lintegral_div (hF i) ha₀.ne.symm ha






lemma unifLIntegrable_empty [IsEmpty ι] : UnifLIntegrable F μ := by simp [UnifLIntegrable]

lemma uniformLIntegrable_empty [IsEmpty ι] : UniformLIntegrable F μ := by simp [UniformLIntegrable]

lemma unifLIntegrable_const {f : α → ℝ≥0∞} (h : ∀ i, F i = f) (hf : ∫⁻ x, f x ∂μ ≠ ∞) :
    UnifLIntegrable F μ := by
  rcases isEmpty_or_nonempty ι with _ | _
  · exact unifLIntegrable_empty
  simp only [unifLIntegrable_def, h, ciSup_const]
  exact tendsto_iSup_setLIntegral_zero hf

lemma tendsto_setLIntegral_preimage_zero {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hf' : ∫⁻ x, f x ∂μ ≠ ∞) :
    Tendsto (fun a ↦ ∫⁻ x in f ⁻¹' Ici a, f x ∂μ) (𝓝 ∞) (𝓝 0) := by
  -- A direct proof is possible (e.g. with the dominated convergence theorem), but leveraging
  -- lemma `unifLIntegrable_const` is faster.
  suffices hF : UniformLIntegrable (ι := {g // g = f}) (fun g x ↦ g.1 x) μ by
    simp only [UniformLIntegrable, ciSup_unique] at hF
    exact hF
  apply UnifLIntegrable.uniformLIntegrable_of_lintegral_lt_top
  · simpa only [Subtype.forall, forall_eq]
  · exact unifLIntegrable_const (by simp) hf'
  · simpa only [ciSup_unique]

-- Harmoniser noms hypothèses
lemma uniformLIntegrable_const {f : α → ℝ≥0∞} (h : ∀ i, F i = f) (hf : AEMeasurable f μ)
    (hf' : ∫⁻ x, f x ∂μ ≠ ∞) :
    UniformLIntegrable F μ := by
  rcases isEmpty_or_nonempty ι with _ | _
  · exact uniformLIntegrable_empty
  apply (unifLIntegrable_const h hf').uniformLIntegrable_of_lintegral_lt_top
  · simpa only [h, forall_const]
  · simpa only [h, ciSup_const]





lemma _root_.Finite.uniformLIntegrable [Finite ι] (h : ∀ i, AEMeasurable (F i) μ)
    (h' : ∀ i, ∫⁻ x, F i x ∂μ ≠ ∞) :
    UniformLIntegrable F μ := by
  sorry

-- TODO : congr lemmas, etc. Voir dans le fichier-frère.
-- TODO : measurepreserving maps


end MeasureTheory
