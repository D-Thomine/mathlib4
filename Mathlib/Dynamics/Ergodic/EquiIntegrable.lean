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

open ENNReal Filter Function Measure Set

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {F : ι → α → ℝ≥0∞}

/- Rename and put in Mathlib.MeasureTheory.Integral.Lebesgue.Markov? -/
lemma measure_preimage_lt_top {f : α → ℝ≥0∞} {a : ℝ≥0∞} (hf : AEMeasurable f μ)
    (hf' : ∫⁻ x, f x ∂μ ≠ ∞) (ha : a ≠ 0) :
    μ (f ⁻¹' Ici a) < ∞ := by
  rcases mul_lt_top_iff.1 <| (mul_meas_ge_le_lintegral₀ hf a).trans_lt hf'.lt_top with h | h | h
  · exact h.2
  · exact (ha h).rec
  · exact h ▸ zero_lt_top

def EquiLIntegrable (μ : Measure α) (F : ι → α → ℝ≥0∞) :=
  Tendsto (fun a ↦ ⨆ i, ∫⁻ x in F i ⁻¹' Ici a, F i x ∂μ) (nhds ∞) (nhds 0)

lemma equiLIntegrable_empty [IsEmpty ι] : EquiLIntegrable μ F := by
  simp [EquiLIntegrable]

lemma equiLIntegrable_const {f : α → ℝ≥0∞} (h : ∀ i, F i = f) (hf : AEMeasurable f μ)
    (hf' : ∫⁻ x, f x ∂μ ≠ ∞) :
    EquiLIntegrable μ F := by
  rcases isEmpty_or_nonempty ι with _ | _
  · exact equiLIntegrable_empty
  simp only [EquiLIntegrable, h, ciSup_const]
  have h₁ : ∀ᶠ a in nhds ∞, AEMeasurable ((f ⁻¹' Ici a).indicator f) μ :=
    Eventually.of_forall fun a ↦ hf.indicator₀ (hf.nullMeasurableSet_preimage measurableSet_Ici)
  have h₂ : ∀ᶠ a in nhds ∞, ∀ᵐ x ∂μ, (f ⁻¹' Ici a).indicator f x ≤ f x := by
    apply Eventually.of_forall fun a ↦ Eventually.of_forall (Pi.le_def.1 ?_)
    exact indicator_le_self' (fun _ _ ↦ zero_le)
  have h₃ : ∀ᵐ x ∂μ, Tendsto (fun a ↦ (f ⁻¹' Ici a).indicator f x) (nhds ∞) (nhds 0) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_eq_top_of_lintegral_ne_top hf hf')]
      with x hx
    rw [← ne_eq] at hx
    apply tendsto_nhds_of_eventually_eq (ENNReal.nhds_top_basis.eventually_iff.2 _)
    obtain ⟨b, bx, b_top⟩ := exists_between hx.lt_top
    exact ⟨b, b_top, fun y hy ↦ indicator_of_notMem (by grind) f⟩
  have key := tendsto_lintegral_filter_of_dominated_convergence' f h₁ h₂ hf' h₃
  simp only [lintegral_const, zero_mul] at key
  exact key.congr fun a ↦ lintegral_indicator₀ (hf.nullMeasurableSet_preimage measurableSet_Ici) f

lemma _root_.Finite.equiLIntegrable [Finite ι] (h : ∀ i, AEMeasurable (F i) μ)
    (h' : ∀ i, ∫⁻ x, F i x ∂μ ≠ ∞) :
    EquiLIntegrable μ F := by
  sorry

-- TODO : measurepreserving maps

private lemma setLIntegral_le_of_equiLIntegrable {f : α → ℝ≥0∞} {A : Set α} (a : ℝ≥0∞)
    (hf : AEMeasurable f μ) (hA : NullMeasurableSet A μ) :
    ∫⁻ x in A, f x ∂μ ≤ a * μ A + ∫⁻ x in f ⁻¹' Ici a, f x ∂μ := by
  obtain ⟨B, _, hB, hAB⟩ := hA.exists_measurable_superset_ae_eq
  rw [← measure_congr hAB, ← setLIntegral_congr hAB]
  obtain ⟨g, g_mes, hfg⟩ := hf
  have h : f ⁻¹' Ici a =ᵐ[μ] g ⁻¹' Ici a := (eventuallyEq_set.2 (hfg.mono (fun x hx ↦ by grind)))
  rw [setLIntegral_congr h, setLIntegral_congr_fun_ae (g := g) hB (hfg.mono (by grind)),
    setLIntegral_congr_fun_ae (f := f) (g := g) (by measurability) (hfg.mono (by grind))]
  rw [← lintegral_inter_add_sdiff g B (g_mes (measurableSet_Ici (a := a))), add_comm]
  apply add_le_add _ (lintegral_mono_set inter_subset_right)
  rw [← setLIntegral_const]
  apply (setLIntegral_mono (measurable_const (a := a)) (by grind)).trans
  exact lintegral_mono_set sdiff_subset

-- TODO : finite measure -> bounded L1

lemma unifLIntegrable_of_equiLIntegrable (hF' : ∀ i, AEMeasurable (F i) μ)
    (hF : EquiLIntegrable μ F) :
    Tendsto (fun ε ↦ ⨆ (i : ι) (A : Set α) (_ : NullMeasurableSet A μ) (_ : μ A < ε),
      ∫⁻ x in A, F i x ∂μ) (nhds 0) (nhds 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ nhds_zero_basis.eventually_iff.2 ?_
  obtain ⟨δ, hδ, hδε⟩ := exists_between hε
  obtain ⟨a, ha, haF⟩ :=
    ENNReal.nhds_top_basis.eventually_iff.1 (ENNReal.tendsto_nhds_zero.1 hF δ hδ)
  obtain ⟨b, hab, hb⟩ := exists_between ha
  have hδε' : ε - δ ≠ 0 := fun p ↦ hδε.not_ge (tsub_eq_zero_iff_le.1 p)
  obtain ⟨κ, hκ, hκb⟩ := ENNReal.exists_pos_mul_lt hb.ne hδε'
  specialize haF (mem_Ioi.2 hab)
  refine ⟨κ, hκ, fun γ hγ ↦ ?_⟩
  simp only [iSup_le_iff] at haF ⊢
  intro i A hA hAμ
  apply (setLIntegral_le_of_equiLIntegrable b (hF' i) hA).trans
  rw [← tsub_add_cancel_of_le hδε.le, mul_comm (a := b)]
  apply add_le_add (hκb.le.trans' _) (haF i)
  exact mul_le_mul_left (hAμ.le.trans (mem_Iio.1 hγ).le) b

lemma unifLIntegrable_of_equiLIntegrable_apply {A : ι → Set α} {l : Filter ι}
    (hF' : ∀ i, AEMeasurable (F i) μ) (hF : EquiLIntegrable μ F)
    (hA : ∀ i, NullMeasurableSet (A i) μ) (h : Tendsto (μ ∘ A) l (nhds 0)) :
    Tendsto (fun i ↦ ∫⁻ x in A i, F i x ∂μ) l (nhds 0) := by
  sorry



end MeasureTheory
