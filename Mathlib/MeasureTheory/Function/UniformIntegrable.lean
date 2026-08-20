/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Uniform integrability

This file contains the definitions for uniform integrability (both in the measure theory sense
as well as the probability theory sense). This file also contains the Vitali convergence theorem
which establishes a relation between uniform integrability, convergence in measure and
Lp convergence.

Uniform integrability plays a vital role in the theory of martingales and most notably is used to
formulate the martingale convergence theorem.

## Main definitions

* `MeasureTheory.UnifIntegrable`: uniform integrability in the measure theory sense.
  In particular, a sequence of functions `f` is uniformly integrable if for all `ε > 0`, there
  exists some `δ > 0` such that for all sets `s` of smaller measure than `δ`, the Lp-norm of
  `f i` restricted to `s` is smaller than `ε` for all `i`.
* `MeasureTheory.UniformIntegrable`: uniform integrability in the probability theory sense.
  In particular, a sequence of measurable functions `f` is uniformly integrable in the
  probability theory sense if it is uniformly integrable in the measure theory sense and
  has uniformly bounded Lp-norm.

## Main results

* `MeasureTheory.unifIntegrable_finite`: a finite sequence of Lp functions is uniformly
  integrable.
* `MeasureTheory.tendsto_Lp_finite_of_tendsto_ae`: a sequence of Lp functions which is uniformly
  integrable converges in Lp if they converge almost everywhere.
* `MeasureTheory.tendstoInMeasure_iff_tendsto_Lp_finite`: Vitali convergence theorem:
  a sequence of Lp functions converges in Lp if and only if it is uniformly integrable
  and converges in measure.

## Tags
uniformly integrable, uniformly absolutely continuous integral, Vitali convergence theorem
-/

@[expose] public section




--TODO
-- Write q < p version for UnifLpTail / UnifIntegrable / etc.
-- Deduce some one-function results from the generic case.
-- Re-structure the file.
-- Check that mathlib compiles








noncomputable section

open scoped NNReal Topology

namespace MeasureTheory

open ENNReal Filter Set

variable {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
  {f g : ι → α → β} {p q : ℝ≥0∞}

/-! ### Definitions

This section deals with uniform integrability in the measure theory sense. -/

/-- Uniform integrability in the measure theory sense.

A sequence of functions `f` is said to be uniformly integrable if for all `ε > 0`, there exists
some `δ > 0` such that for all sets `s` with measure less than `δ`, the Lp-norm of `f i`
restricted to `s` is less than `ε`.

Uniform integrability is also known as uniformly absolutely continuous integrals. -/
def UnifIntegrable {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  Tendsto (fun ε ↦ ⨆ (i : ι) (s : Set α) (_ : μ s ≤ ε), eLpNorm (f i) p (μ.restrict s)) (𝓝 0) (𝓝 0)

/-- A family of functions has `UnifTail` if the measure of the tail subsets `{ x | M ≤ ‖f i x‖ₑ }`
decay uniformly to `0`. -/
def UnifTail {_ : MeasurableSpace α} (f : ι → α → β) (μ : Measure α) : Prop :=
  Tendsto (fun M ↦ ⨆ (i : ι), μ { x | M ≤ ‖f i x‖ₑ }) (𝓝 ∞) (𝓝 0)

/-- A family of functions has `UnifLpTail` if the `eLpNorm` carried by the tail subsets
`{ x | M ≤ ‖f i x‖ₑ }` decay uniformly to `0`. -/
def UnifLpTail {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  Tendsto (fun M ↦ ⨆ (i : ι), eLpNorm (f i) p (μ.restrict { x | M ≤ ‖f i x‖ₑ })) (𝓝 ∞) (𝓝 0)

/-- In probability theory, a family of measurable functions is uniformly integrable if it is
uniformly integrable in the measure theory sense and is uniformly bounded. -/
structure UniformIntegrable {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) :
  Prop where
  protected aestronglyMeasurable : ∀ i, AEStronglyMeasurable (f i) μ
  protected unifIntegrable : UnifIntegrable f p μ
  protected bdd : ⨆ i, eLpNorm (f i) p μ < ∞

/-! ### Basic properties -/

section UnifIntegrable

theorem unifIntegrable_mk_iff :
    UnifIntegrable f p μ ↔ Tendsto (fun ε ↦ ⨆ (i : ι) (s : Set α) (_ : MeasurableSet s)
      (_ : μ s ≤ ε), eLpNorm (f i) p (μ.restrict s)) (𝓝 0) (𝓝 0) := by
  rw [UnifIntegrable, iff_iff_eq]
  congrm Tendsto (fun ε ↦ ⨆ i, ?_) _ _
  refine le_antisymm (iSup₂_le fun s hsμ ↦ ?_) (iSup₂_le_iSup _ _)
  obtain ⟨t, hst, ht, hμt⟩ := exists_measurable_superset μ s
  grw [← le_iSup₂ t ht, ← le_iSup _ (hμt ▸ hsμ), eLpNorm_mono_measure _ (μ.restrict_mono_set hst)]

/-- A characterization of `UnifIntegrable` families. This version does not assume that the sets `s`
are measurable, and is convenient for applying the hypothesis that a family is `UnifIntegrable`.
See `unifIntegrable_iff'` for a version where the sets `s` are assumed measurable. -/
theorem unifIntegrable_iff :
  UnifIntegrable f p μ ↔
    ∀ ε > 0, ∃ δ > 0, ∀ i s, μ s ≤ δ → eLpNorm (f i) p (μ.restrict s) ≤ ε := by
  rw [UnifIntegrable, ENNReal.tendsto_nhds_zero]
  apply forall₂_congr fun ε hε ↦ ?_
  rw [nhds_zero_basis_Iic.eventually_iff]
  apply exists_congr fun δ ↦ and_congr_right fun hδ ↦ ?_
  simp only [mem_Iic, iSup_le_iff]
  exact ⟨fun h ↦ h (le_refl δ), fun h x hx i s hs ↦ h i s (hs.trans hx)⟩

/-- A characterization of `UnifIntegrable` families. This version assumes that the sets `s` are
measurable, and is convenient for proving that a family is `UnifIntegrable`. See
`unifIntegrable_iff` for a version where the sets `s` are not assumed measurable. -/
theorem unifIntegrable_iff' :
  UnifIntegrable f p μ ↔
    ∀ ε > 0, ∃ δ > 0, ∀ i s, MeasurableSet s → μ s ≤ δ → eLpNorm (f i) p (μ.restrict s) ≤ ε := by
  rw [unifIntegrable_mk_iff, ENNReal.tendsto_nhds_zero]
  apply forall₂_congr fun ε hε ↦ ?_
  rw [nhds_zero_basis_Iic.eventually_iff]
  apply exists_congr fun δ ↦ and_congr_right fun hδ ↦ ?_
  simp only [mem_Iic, iSup_le_iff]
  exact ⟨fun h ↦ h (le_refl δ), fun h x hx i s hs hμs ↦ h i s hs (hμs.trans hx)⟩

@[simp]
theorem unifIntegrable_of_isEmpty [IsEmpty ι] : UnifIntegrable f p μ := by simp [UnifIntegrable]

@[simp]
theorem unifIntegrable_zero_meas : UnifIntegrable f p (0 : Measure α) := by simp [UnifIntegrable]

@[simp]
theorem unifIntegrable_zero_exponent : UnifIntegrable f 0 μ := by simp [UnifIntegrable]

protected theorem UnifIntegrable.ae_mono (hg : UnifIntegrable g p μ)
    (hfg : ∀ i, (‖f i ·‖ₑ) ≤ᵐ[μ] (‖g i ·‖ₑ)) :
    UnifIntegrable f p μ := by
  refine tendsto_nhds_bot_mono hg (Eventually.of_forall fun ε ↦ ?_)
  simp only
  gcongr
  exact eLpNorm_mono_enorm_ae ((hfg i).filter_mono ae_restrict_le)

protected theorem UnifIntegrable.ae_eq (hf : UnifIntegrable f p μ) (hfg : ∀ i, f i =ᵐ[μ] g i) :
    UnifIntegrable g p μ :=
  hf.ae_mono fun i ↦ ((hfg i).symm.fun_comp _).le

theorem unifIntegrable_congr_ae (hfg : ∀ i, f i =ᵐ[μ] g i) :
    UnifIntegrable f p μ ↔ UnifIntegrable g p μ :=
  ⟨fun hf ↦ hf.ae_eq hfg, fun hg ↦ hg.ae_eq fun n ↦ (hfg n).symm⟩

/-- Uniform integrability is preserved by restriction of the measure to a set. -/
protected theorem UnifIntegrable.restrict (hf : UnifIntegrable f p μ) (s : Set α) :
    UnifIntegrable f p (μ.restrict s) := by
  rw [unifIntegrable_mk_iff]
  apply tendsto_nhds_bot_mono hf (nhds_zero_basis.eventually_iff.2 ?_)
  refine ⟨∞, zero_lt_top, fun ε hε ↦ iSup_mono fun i ↦ ?_⟩
  simp only [iSup_le_iff]
  intro t ht hμt
  grw [μ.restrict_restrict ht, ← le_iSup₂ (t ∩ s) (μ.restrict_apply ht ▸ hμt)]

/-- Uniform integrability is preserved by restriction of the functions to a set. -/
protected theorem UnifIntegrable.indicator (hf : UnifIntegrable f p μ) (s : Set α) :
    UnifIntegrable (fun i ↦ s.indicator (f i)) p μ :=
  hf.ae_mono fun i ↦ Eventually.of_forall fun x ↦ enorm_indicator_le_enorm_self (f i) x

protected theorem UnifIntegrable.comp {ι' : Type*} (g : ι' → ι) (hf : UnifIntegrable f p μ) :
    UnifIntegrable (f ∘ g) p μ := by
  refine tendsto_nhds_bot_mono hf (Eventually.of_forall fun ε ↦ ?_)
  simp only [Function.comp_apply]
  exact iSup_comp_le (f := fun i ↦  ⨆ (s : Set α) (_ : μ s ≤ ε), eLpNorm (f i) p (μ.restrict s)) _

protected theorem UnifIntegrable.add (hf : UnifIntegrable f p μ) (hg : UnifIntegrable g p μ)
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ) (hg_meas : ∀ i, AEStronglyMeasurable (g i) μ) :
    UnifIntegrable (f + g) p μ := by
  rw [unifIntegrable_mk_iff]
  apply tendsto_nhds_bot_mono (f := fun ε ↦ p.LpAddConst *
    ((⨆ (i : ι) (s : Set α) (_ : μ s ≤ ε), eLpNorm (f i) p (μ.restrict s)) +
      ⨆ (i : ι) (s : Set α) (_ : μ s ≤ ε), eLpNorm (g i) p (μ.restrict s)))
  · rw [bot_eq_zero]; nth_rw 2 [← mul_zero p.LpAddConst]
    apply ENNReal.Tendsto.const_mul _ (.inr p.LpAddConst_lt_top.ne)
    nth_rw 2 [← zero_add 0]
    exact Tendsto.add hf hg
  · apply Eventually.of_forall fun ε ↦ ?_
    simp only [Pi.add_apply, iSup_le_iff]
    intro i s hs hsμ
    apply (eLpNorm_add_le' ((hf_meas i).mono_measure μ.restrict_le_self)
      ((hg_meas i).mono_measure μ.restrict_le_self) p).trans
    apply mul_le_mul_right (add_le_add _ _) <;>
    apply (le_iSup _ i).trans' ((le_iSup _ s).trans' (by simp [hsμ]))

protected theorem UnifIntegrable.neg (hf : UnifIntegrable f p μ) : UnifIntegrable (-f) p μ := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ ?_
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hf ε hε] with s hs
  simpa only [Pi.neg_apply, eLpNorm_neg]

protected theorem UnifIntegrable.sub (hf : UnifIntegrable f p μ) (hg : UnifIntegrable g p μ)
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ) (hg_meas : ∀ i, AEStronglyMeasurable (g i) μ) :
    UnifIntegrable (f - g) p μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg hf_meas fun i => (hg_meas i).neg

end UnifIntegrable

section UnifTail

@[simp]
theorem unifTail_of_isEmpty [IsEmpty ι] : UnifTail f μ := by simp [UnifTail]

@[simp]
theorem unifTail_zero_meas : UnifTail f (0 : Measure α) := by simp [UnifTail]

protected theorem UnifTail.ae_mono (hg : UnifTail g μ) (hfg : ∀ i, (‖f i ·‖ₑ) ≤ᵐ[μ] (‖g i ·‖ₑ)) :
    UnifTail f μ := by
  refine tendsto_nhds_bot_mono hg (Eventually.of_forall fun M ↦ ?_)
  refine iSup_mono fun i ↦ measure_mono_ae ?_
  filter_upwards [hfg i] with x hx hxF
  exact hxF.trans hx

protected theorem UnifTail.ae_eq (hf : UnifTail f μ) (hfg : ∀ i, f i =ᵐ[μ] g i) : UnifTail g μ :=
  hf.ae_mono fun i ↦ ((hfg i).symm.fun_comp _).le

theorem unifTail_congr_ae (hfg : ∀ i, f i =ᵐ[μ] g i) : UnifTail f μ ↔ UnifTail g μ :=
  ⟨fun hf ↦ hf.ae_eq hfg, fun hg ↦ hg.ae_eq fun n ↦ (hfg n).symm⟩

protected theorem UnifTail.mono_measure {ν : Measure α} (hf : UnifTail f μ) (h : ν ≤ μ) :
    UnifTail f ν :=
  tendsto_nhds_bot_mono hf (Eventually.of_forall fun _ ↦ iSup_mono fun _ ↦ ν.measure_mono_left h _)

protected theorem UnifTail.restrict (h : UnifTail f μ) (s : Set α) : UnifTail f (μ.restrict s) :=
  h.mono_measure μ.restrict_le_self

protected theorem UnifTail.add (hf : UnifTail f μ) (hg : UnifTail g μ) : UnifTail (f + g) μ := by
  -- If `c ≤ f i + g i`, then either `c / 2 ≤ f i` or `c / 2 ≤ g i`.
  -- By this observation, `{ c ≤ f i + g i } ⊆ { c / 2 ≤ f i } ∪ { c / 2 ≤ g i }`,
  -- and we can control the measure of the latter set.
  rw [UnifTail, ENNReal.tendsto_nhds_zero] at hf hg ⊢
  intro ε hε
  obtain ⟨a, ha, haμ⟩ := _root_.nhds_top_basis.eventually_iff.1 (hf (ε / 2) (ε.half_pos hε.ne'))
  obtain ⟨b, hb, hbμ⟩ := _root_.nhds_top_basis.eventually_iff.1 (hg (ε / 2) (ε.half_pos hε.ne'))
  refine _root_.nhds_top_basis.eventually_iff.2 ⟨max (2 * a) (2 * b), by finiteness, fun c hc ↦ ?_⟩
  simp only [mem_Ioi, sup_lt_iff, iSup_le_iff, Pi.add_apply] at hc haμ hbμ ⊢
  intro i
  apply le_trans (b := μ ({ x | c / 2 ≤ ‖f i x‖ₑ} ∪ { x | c / 2 ≤ ‖g i x‖ₑ}))
  · refine measure_mono fun x ↦ ?_
    contrapose
    simp only [mem_union, mem_ofPred_eq, not_or, not_le, and_imp]
    intro hfx hgx
    grw [enorm_add_le, ENNReal.add_lt_add hfx hgx, c.add_halves]
  · rw [mul_comm 2 _, ← ENNReal.lt_div_iff_mul_lt (.inl two_ne_zero) (.inl ofNat_ne_top),
      mul_comm 2 _, ← ENNReal.lt_div_iff_mul_lt (.inl two_ne_zero) (.inl ofNat_ne_top)] at hc
    grw [measure_union_le _ _, add_le_add (haμ hc.1 i) (hbμ hc.2 i), ε.add_halves]

end UnifTail

section UnifLpTail

@[simp]
theorem unifLpTail_of_isEmpty [IsEmpty ι] : UnifLpTail f p μ := by simp [UnifLpTail]

@[simp]
theorem unifLpTail_zero_meas : UnifLpTail f p (0 : Measure α) := by simp [UnifLpTail]

@[simp]
theorem unifLpTail_zero_exponent : UnifLpTail f 0 μ := by simp [UnifLpTail]

protected theorem UnifLpTail.ae_mono (hg : UnifLpTail g p μ)
    (hfg : ∀ i, (‖f i ·‖ₑ) ≤ᵐ[μ] (‖g i ·‖ₑ)) :
    UnifLpTail f p μ := by
  refine tendsto_nhds_bot_mono hg (Eventually.of_forall fun M ↦ iSup_mono fun i ↦ ?_)
  apply (eLpNorm_mono_enorm_ae (ae_restrict_of_ae (hfg i))).trans
  apply eLpNorm_mono_measure
  apply μ.restrict_mono_ae
  filter_upwards [hfg i] with x hx
  simp only [le_Prop_eq]
  exact hx.trans'

protected theorem UnifLpTail.ae_eq (hf : UnifLpTail f p μ) (hfg : ∀ i, f i =ᵐ[μ] g i) :
    UnifLpTail g p μ :=
  hf.ae_mono fun i ↦ ((hfg i).symm.fun_comp _).le

theorem unifLpTail_congr_ae (hfg : ∀ i, f i =ᵐ[μ] g i) :
    UnifLpTail f p μ ↔ UnifLpTail g p μ :=
  ⟨fun hf ↦ hf.ae_eq hfg, fun hg ↦ hg.ae_eq fun n ↦ (hfg n).symm⟩

protected theorem UnifLpTail.mono_measure {ν : Measure α} (hf : UnifLpTail f p μ) (h : ν ≤ μ) :
    UnifLpTail f p ν := by
  refine tendsto_nhds_bot_mono hf (Eventually.of_forall fun M ↦ iSup_mono fun i ↦ ?_)
  apply eLpNorm_mono_measure
  exact (ν.restrict_mono_measure h _)

protected theorem UnifLpTail.restrict (h : UnifLpTail f p μ) (s : Set α) :
    UnifLpTail f p (μ.restrict s) :=
  h.mono_measure μ.restrict_le_self

theorem unifLpTail_top_iff (hf : ∀ i, AEStronglyMeasurable (f i) μ) :
    UnifLpTail f ∞ μ ↔ ⨆ i, eLpNormEssSup (f i) μ < ∞ := by
  constructor <;> intro h
  · obtain ⟨M, hM, hMf⟩ := (nhds_top_basis_Ici.tendsto_iff nhds_zero_basis_Iic).1 h 1 zero_lt_one
    simp only [mem_Ici, eLpNorm_exponent_top, mem_Iic, iSup_le_iff] at hMf
    apply iSup_lt_iff.2 ⟨max M 1, by finiteness, fun i ↦ eLpNormEssSup_le_of_ae_enorm_bound ?_⟩
    have key := ae_le_eLpNormEssSup (f := f i) (μ := μ.restrict { x | M ≤ ‖f i x‖ₑ })
    rw [ae_restrict_iff₀] at key; swap
    · exact (nullMeasurableSet_le (hf i).enorm aemeasurable_const).mono μ.restrict_le_self
    simp only [le_max_iff, or_iff_not_imp_left]
    filter_upwards [key] with x hx hxM
    exact (hx (not_le.1 hxM).le).trans (hMf M le_rfl i)
  · apply EventuallyEq.tendsto (_root_.nhds_top_basis.eventually_iff.2 _)
    refine ⟨⨆ i, eLpNormEssSup (f i) μ, h, fun m hm ↦ ?_⟩
    simp only [eLpNorm_exponent_top, iSup_eq_zero, eLpNormEssSup_eq_zero_iff]
    intro i
    apply (ae_restrict_iff₀ _).2; swap
    · apply NullMeasurableSet.mono _ μ.restrict_le_self
      exact (hf i).nullMeasurableSet_eq_fun aestronglyMeasurable_zero
    filter_upwards [ae_le_eLpNormEssSup (f := f i)] with x hx hxm
    grind [le_iSup (fun j ↦ eLpNormEssSup (f j) μ) i]

theorem unifLpTail_iff_nnreal (hf : ∀ i, AEStronglyMeasurable (f i) μ) : UnifLpTail f p μ ↔
    ∀ ε > 0, ∃ M : ℝ≥0, ∀ i, eLpNorm ({ x | M ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ε := by
  rw [UnifLpTail, nhds_top_basis_Ici.tendsto_iff nhds_zero_basis_Iic]
  constructor <;> intro h ε hε <;> simp only [mem_Ici, mem_Iic, iSup_le_iff] at h ⊢
  · obtain ⟨M, hM, hMf⟩ := h ε hε
    refine ⟨M.toNNReal, fun i ↦ (hMf M le_rfl i).trans_eq' ?_⟩
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict
      (nullMeasurableSet_le aemeasurable_const (hf i).enorm)]
    congr 3
    ext x
    nth_rw 1 [enorm_eq_nnnorm, ← coe_toNNReal hM.ne, coe_le_coe]
  · obtain ⟨M, hMf⟩ := h ε hε
    refine ⟨M, coe_lt_top, fun m hm i ↦ (hMf i).trans' ?_⟩
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict
      (nullMeasurableSet_le aemeasurable_const (hf i).enorm)]
    refine eLpNorm_mono_enorm fun x ↦ enorm_indicator_le_of_subset ?_ (f i) x
    simp only [ofPred_subset_ofPred, enorm_eq_nnnorm]
    exact fun x hx ↦ coe_le_coe.1 (hm.trans hx)

end UnifLpTail

section UniformIntegrable

@[simp]
theorem uniformIntegrable_of_isEmpty [IsEmpty ι] : UniformIntegrable f p μ :=
  ⟨by simp, unifIntegrable_of_isEmpty, by simp⟩

@[simp]
theorem uniformIntegrable_zero_meas [MeasurableSpace α] : UniformIntegrable f p (0 : Measure α) :=
  ⟨fun _ ↦ aestronglyMeasurable_zero_measure _, unifIntegrable_zero_meas, by simp⟩

theorem UniformIntegrable.ae_eq {g : ι → α → β} (hf : UniformIntegrable f p μ)
    (hfg : ∀ i, f i =ᵐ[μ] g i) : UniformIntegrable g p μ := by
  obtain ⟨hfm, hunif, hC⟩ := hf
  refine ⟨fun i ↦ (hfm i).congr (hfg i), (unifIntegrable_congr_ae hfg).1 hunif, hC.trans_eq' ?_⟩
  exact iSup_congr fun i ↦ eLpNorm_congr_ae (hfg i)

theorem uniformIntegrable_congr_ae {g : ι → α → β} (hfg : ∀ n, f n =ᵐ[μ] g n) :
    UniformIntegrable f p μ ↔ UniformIntegrable g p μ :=
  ⟨fun h => h.ae_eq hfg, fun h => h.ae_eq fun i => (hfg i).symm⟩

protected theorem UniformIntegrable.memLp (hf : UniformIntegrable f p μ) (i : ι) :
    MemLp (f i) p μ :=
  ⟨hf.aestronglyMeasurable i, (le_iSup _ i).trans_lt hf.bdd⟩

end UniformIntegrable

/-! ### Relations between versions of uniform integrability -/

-- Auxiliary lemma in the proofs of sufficient conditions for uniform integrability.
private lemma eLpNorm_restrict_le_const_add_eLpNorm (p : ℝ≥0∞) {f : α → β}
    (hf : AEStronglyMeasurable f μ) (s : Set α) (M : ℝ≥0∞) :
    eLpNorm f p (μ.restrict s) ≤ p.LpAddConst *
      (M * μ s ^ p.toReal⁻¹ + eLpNorm f p (μ.restrict { x | M ≤ ‖f x‖ₑ })) := by
  have hmeas : NullMeasurableSet { y | M ≤ ‖(f y)‖ₑ } μ :=
    nullMeasurableSet_le aemeasurable_const hf.enorm
  -- We first deal with the degenerate cases `p = 0` and `p = ∞`.
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  rcases eq_or_ne p ∞ with rfl | hp'
  · apply (eLpNorm_restrict_le f ∞ μ s).trans
    simp only [eLpNorm_exponent_top, LpAddConst, mem_Ioo, zero_lt_top, not_top_lt, and_false,
      ↓reduceIte, toReal_top, _root_.inv_zero, rpow_zero, mul_one, one_mul]
    nth_rw 1 [← piecewise_same { x | M ≤ ‖f x‖ₑ } f, eLpNormEssSup_piecewise f f hmeas, add_comm]
    apply (max_le_add_of_nonneg bot_le bot_le).trans (add_le_add_right _ _)
    apply eLpNormEssSup_le_of_ae_enorm_bound
    filter_upwards [ae_restrict_mem₀ hmeas.compl] with x hx
    grind
  -- Without loss of generality, `s` can be assumed measurable.
  obtain ⟨t, hst, ht, htμ⟩ := exists_measurable_superset μ s
  apply (eLpNorm_mono_measure f (μ.restrict_mono_set hst)).trans
  rw [← htμ]; clear htμ hst s
  -- Main argument : on `{ x | M ≤ ‖f x‖ₑ }ᶜ`, the function `‖f x‖ₑ` is bounded by `M`.
  let g : α → ℝ≥0∞ := fun x ↦ M + ({ y | M ≤ ‖(f y)‖ₑ }.indicator (fun y ↦ ‖f y‖ₑ)) x
  have h : ∀ᵐ x ∂(μ.restrict t), ‖f x‖ₑ ≤ ‖g x‖ₑ := by
    filter_upwards [ae_restrict_mem₀ ht.nullMeasurableSet] with x hx
    by_cases hxf : x ∈ { y | M ≤ ‖(f y)‖ₑ }
    · simp [hxf, g]
    · simp [hxf, g, (not_le.1 (notMem_ofPred_iff.1 hxf)).le]
  -- It remains to use a (generalised) triangle inequality.
  replace hmeas : NullMeasurableSet _ (μ.restrict t) := hmeas.mono μ.restrict_le_self
  apply (eLpNorm_mono_enorm_ae h).trans; clear h
  apply (eLpNorm_add_le' aestronglyMeasurable_const _ p).trans; swap
  · apply aestronglyMeasurable_iff_aemeasurable.2
    exact (hf.enorm.mono_measure μ.restrict_le_self).indicator₀ hmeas
  apply mul_right_mono (add_le_add _ _)
  · simp [eLpNorm_const' M hp hp']
  · rw [eLpNorm_indicator_eq_eLpNorm_restrict hmeas]
    apply eLpNorm_mono_measure
    exact (Measure.restrict_mono_measure μ.restrict_le_self { y | M ≤ ‖(f y)‖ₑ })

theorem UnifLpTail.unifIntegrable (hp : p ≠ ∞) (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (h : UnifLpTail f p μ) :
    UnifIntegrable f p μ := by
  rcases eq_or_ne p 0 with rfl | hp'
  · exact unifIntegrable_zero_exponent
  -- The proof relies on `eLpNorm_restrict_le_const_add_eLpNorm`,
  -- with a good choice of parameter `M` depending on the parameter `ε`
  -- in the definition of `UnifIntegrable`.
  -- On the one hand, `μ s` is of size at most `ε`, so we want `M(ε) * ε ^ p.toReal⁻¹` to vanish.
  -- On the other hand, we want `M(ε)` to diverge in order to use `UnifLpTail f p μ`.
  -- We choose `M(ε) = ε ^ (-r)` with `0 < r < p.toReal⁻¹`.
  obtain ⟨r, hr₀, hrp⟩ := exists_between (inv_pos.2 (toReal_pos hp' hp))
  apply tendsto_nhds_bot_mono' (f := fun ε ↦ p.LpAddConst * (ε ^ (-r) * ε ^ p.toReal⁻¹ +
    ⨆ i, eLpNorm (f i) p (μ.restrict { x | ε ^ (-r) ≤ ‖f i x‖ₑ })))
  · have hr_pow := (continuous_rpow_const (y := -r)).tendsto 0
    rw [zero_rpow_of_neg (Left.neg_neg_iff.2 hr₀)] at hr_pow
    have hrp_pow := (continuous_rpow_const (y := p.toReal⁻¹ - r)).tendsto 0
    rw [zero_rpow_of_pos (sub_pos_of_lt hrp)] at hrp_pow
    rw [bot_eq_zero]; nth_rw 2 [← mul_zero p.LpAddConst]
    apply ENNReal.Tendsto.const_mul _ (.inr p.LpAddConst_lt_top.ne)
    rw [← Pi.add_def]; nth_rw 2 [← zero_add 0]
    refine (hrp_pow.congr' ?_).add (h.comp hr_pow)
    refine (nhds_zero_basis.eventually_iff).2 ⟨∞, zero_lt_top, fun ε hε ↦ ?_⟩
    simp only
    rw [sub_eq_add_neg, rpow_add_of_add_pos hε.ne _ (-r) (by simp [hrp]), mul_comm]
  · intro ε
    simp only [iSup_le_iff]
    refine fun i s hsμ ↦ (eLpNorm_restrict_le_const_add_eLpNorm p (hf i) s (ε ^ (-r))).trans ?_
    apply mul_le_mul_right (add_le_add _ (le_iSup _ i)) p.LpAddConst
    exact mul_le_mul_right (rpow_le_rpow hsμ (by positivity)) (ε ^ (-r))

@[deprecated (since := "2026-08-20")] alias unifIntegrable_of := UnifLpTail.unifIntegrable

theorem iSup_eLpNorm_lt_of [IsFiniteMeasure μ] (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (h : UnifLpTail f p μ) :
    ⨆ i, eLpNorm (f i) p μ < ∞ := by
  -- The proof relies on `eLpNorm_restrict_le_const_add_eLpNorm`. Choose `s = univ` and
  -- `M` such that `eLpNorm f p (μ.restrict { x | M ≤ ‖f x‖ₑ })) < ∞`.
  have _ := @ENNReal.nhdsLT_neBot ∞ (NeZero.mk zero_ne_top.symm)
  obtain ⟨M, hM, hMf⟩ := (nhds_zero_basis.tendsto_right_iff.1 h ∞ zero_lt_top).exists_lt
  apply lt_of_le_of_lt (b := p.LpAddConst *
      (M * μ univ ^ p.toReal⁻¹ + ⨆ i, eLpNorm (f i) p (μ.restrict { x | M ≤ ‖f i x‖ₑ })))
  · apply iSup_le_iff.2 fun i ↦ ?_
    nth_rw 1 [← μ.restrict_univ]
    apply (eLpNorm_restrict_le_const_add_eLpNorm p (hf i) univ M).trans
    apply mul_le_mul_right (add_le_add_right _ _)
    exact le_iSup (fun i ↦ eLpNorm (f i) p (μ.restrict { x | M ≤ ‖f i x‖ₑ })) i
  · exact mul_lt_top p.LpAddConst_lt_top (by finiteness)

theorem UnifLpTail.uniformIntegrable [IsFiniteMeasure μ] (hp : p ≠ ∞)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (h : UnifLpTail f p μ) :
    UniformIntegrable f p μ :=
  ⟨hf, h.unifIntegrable hp hf, iSup_eLpNorm_lt_of hf h⟩

@[deprecated (since := "2026-08-20")] alias uniformIntegrable_of := UnifLpTail.uniformIntegrable

theorem unifLpTail_of (h : UnifIntegrable f p μ) (h' : UnifTail f μ) :
    UnifLpTail f p μ := by
  refine (nhds_zero_basis_Iic.tendsto_right_iff).2 fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hδf⟩ := (nhds_zero_basis_Iic.tendsto_iff nhds_zero_basis_Iic).1 h ε hε
  filter_upwards [(nhds_zero_basis_Iic.tendsto_right_iff).1 h' δ hδ] with M hM
  simp only [mem_Iic, iSup_le_iff] at hδf hM ⊢
  exact fun i ↦ hδf δ le_rfl i { x | M ≤ ‖f i x‖ₑ } (hM i)

theorem unifTail_of (hp : p ≠ 0) (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (h : ⨆ i, eLpNorm (f i) p μ ≠ ∞) :
    UnifTail f μ := by
  -- The case `p = ∞` is dealt with separately. In this case, the tails `{ x | M ≤ ‖f i x‖ₑ}`
  -- are a.e. empty as soon as `M` is large than all the `eLpNormEssSup (f i) μ`.
  rcases eq_or_ne p ∞ with rfl | hp'
  · apply EventuallyEq.tendsto
    obtain ⟨M, hMf, hM⟩ := exists_between h.lt_top
    filter_upwards [_root_.nhds_top_basis_Ici.mem_of_mem hM] with m hm
    refine iSup_eq_zero.2 fun i ↦ ?_
    apply measure_mono_null _ (meas_eLpNormEssSup_lt (f := f i))
    simp only [eLpNorm_exponent_top, mem_Ici, ofPred_subset_ofPred] at hMf hm ⊢
    intro x hx
    grw [le_iSup (fun j ↦ eLpNormEssSup (f j) μ) i, hMf, hm, hx]
  -- If `p ≠ ∞`, we use Markov's inequality for `eLpNorm`.
  apply tendsto_nhds_bot_mono (f := fun M ↦ (⨆ i, eLpNorm (f i) p μ) ^ p.toReal / M ^ p.toReal)
  · rw [bot_eq_zero, ← div_top (a := (⨆ i, eLpNorm (f i) p μ) ^ p.toReal)]
    exact Tendsto.const_div (tendsto_rpow_at_top (toReal_pos hp hp'))
      (.inr <| rpow_ne_top_of_nonneg toReal_nonneg h)
  · filter_upwards [_root_.nhds_top_basis.mem_of_mem zero_lt_top] with M hM
    simp only [iSup_le_iff]
    intro i
    rw [ENNReal.le_div_iff_mul_le (.inl <| (rpow_pos_of_nonneg hM toReal_nonneg).ne')
      (.inr <| rpow_ne_top_of_nonneg toReal_nonneg h), mul_comm]
    apply (mul_meas_ge_le_pow_eLpNorm' μ hp hp' (hf i) M).trans
    exact rpow_le_rpow (le_iSup (fun i ↦ eLpNorm (f i) p μ) i) toReal_nonneg

theorem UniformIntegrable.unifLpTail (hfu : UniformIntegrable f p μ) : UnifLpTail f p μ := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  exact unifLpTail_of hfu.unifIntegrable (unifTail_of hp hfu.1 hfu.bdd.ne)

theorem UnifLpTail.unifTail (hp : p ≠ 0) (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (h : UnifLpTail f p μ) :
    UnifTail f μ := by
  rcases eq_or_ne p ∞ with rfl | hp'
  · simp only [unifLpTail_top_iff hf, ← eLpNorm_exponent_top, lt_top_iff_ne_top] at h
    exact unifTail_of top_ne_zero hf h
  apply tendsto_nhds_bot_mono (f := fun M ↦
    ((⨆ i, eLpNorm (f i) p (μ.restrict { x | M ≤ ‖f i x‖ₑ })) ^ p.toReal) / M ^ p.toReal)
  · rw [bot_eq_zero, ← ENNReal.zero_div (a := ∞)]
    apply ENNReal.Tendsto.div _ (.inr top_ne_zero) (tendsto_rpow_at_top (toReal_pos hp hp'))
      (.inr zero_ne_top)
    exact (continuous_rpow_const.tendsto' 0 0 (zero_rpow_of_pos (toReal_pos hp hp'))).comp h
  · filter_upwards [_root_.nhds_top_basis.mem_of_mem zero_lt_top] with M hM
    refine iSup_le_iff.2 fun i ↦ ?_
    -- For `M < ∞`, this follows from Markov's inequality.
    -- A specific argument is needed for `M = ∞`: the LHS is zero because the `eLpNorm` of `f i`
    -- on this set vanishes.
    rcases eq_top_or_lt_top M with rfl | hM'
    · apply le_of_eq_of_le _ zero_le
      simp only [top_le_iff, ← μ.restrict_apply_self, measure_eq_zero_iff_ae_notMem, mem_ofPred_eq]
      have key := eq_of_tendsto_nhds h
      simp only [top_le_iff, iSup_eq_zero] at key
      specialize key i
      rw [← eLpNorm_enorm (f i), eLpNorm_eq_zero_iff
        ((hf i).enorm.mono_measure μ.restrict_le_self).aestronglyMeasurable hp] at key
      filter_upwards [key] with x hx
      simp [hx, - enorm_ne_top] -- Avoids `enorm_ne_top`, which doesn't extend to ESemiNormedMonoids
    · rw [ENNReal.le_div_iff_mul_le (.inl _) (.inl (by finiteness)), mul_comm]; swap
      · grind [rpow_eq_zero_iff_of_pos (toReal_pos hp hp')]
      rw [← rpow_inv_le_iff (toReal_pos hp hp'), mul_rpow_of_nonneg _ _ (by positivity), ← rpow_mul,
      mul_inv_cancel₀ (toReal_pos hp hp').ne', rpow_one, ← one_div, ← μ.restrict_apply_self]
      apply (le_iSup _ i).trans'
      apply le_eLpNorm_of_bddBelow' hp hp' M _ (by simp)
      exact (nullMeasurableSet_le aemeasurable_const (hf i).enorm).mono (μ.restrict_le_self)

theorem UnifLpTail.add (hf : UnifLpTail f p μ) (hg : UnifLpTail g p μ)
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ) (hg_meas : ∀ i, AEStronglyMeasurable (g i) μ) :
    UnifLpTail (f + g) p μ := by
  -- Versions of this theorem have already been proved for `UnifIntegrable` and `UnifTail`.
  -- `UnifLpTail` is equivalent to `UnifIntegrable ∧ UnifTail`,
  -- outside of the cases `p = 0`, `p = ∞` which are dealt with separately.
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  rcases eq_or_ne p ∞ with rfl | hp'
  · simp only [hf_meas, implies_true, unifLpTail_top_iff, hg_meas, Pi.add_apply,
      fun i ↦ (hf_meas i).add (hg_meas i)] at hf hg ⊢
    apply iSup_lt_iff.2 ⟨(⨆ j, eLpNormEssSup (f j) μ) + ⨆ j, eLpNormEssSup (g j) μ,
      add_lt_top.2 ⟨hf, hg⟩, fun i ↦ ?_⟩
    exact eLpNormEssSup_add_le.trans (add_le_add (le_iSup (fun j ↦ eLpNormEssSup (f j) μ) i)
      (le_iSup (fun j ↦ eLpNormEssSup (g j) μ) i))
  apply unifLpTail_of
  · exact (hf.unifIntegrable hp' hf_meas).add (hg.unifIntegrable hp' hg_meas) hf_meas hg_meas
  · exact (hf.unifTail hp hf_meas).add (hg.unifTail hp hg_meas)

/-! ### Single functions and finite families -/

section

variable {f : α → β}

theorem MemLp.restrict_norm_ge_eq_zero (hf : MemLp f ∞ μ) :
    ∀ᶠ M in 𝓝 ∞, μ.restrict { x | M ≤ ‖f x‖ₑ } = 0 := by
  refine _root_.nhds_top_basis.eventually_iff.2 ⟨eLpNormEssSup f μ, hf.2, fun x hx ↦ ?_⟩
  suffices h : μ.restrict { y | x ≤ ‖f y‖ₑ } = 0 by simp [h]
  exact μ.restrict_eq_zero.2 (μ.mono_null (by grind) (meas_eLpNormEssSup_lt (f := f)))

theorem MemLp.tendsto_iSup_eLpNorm_restrict_nhds_zero_of_lt (hpq : q < p) (hf : MemLp f p μ) :
    Tendsto (fun ε ↦ ⨆ (s : Set α) (_ : μ s ≤ ε), eLpNorm f q (μ.restrict s)) (𝓝 0) (𝓝 0) := by
  rcases eq_or_ne q 0 with rfl | hq₀
  · simp
  apply tendsto_nhds_bot_mono (f := fun ε ↦ (eLpNorm f p μ) * ε ^ (q.toReal⁻¹ - p.toReal⁻¹))
  · apply tendsto_const_mul_rpow_nhds_zero_of_pos hf.2.ne
    rw [sub_pos]
    rcases eq_or_ne p ∞ with rfl | hp_top
    · simp [toReal_pos hq₀ hpq.ne]
    · exact inv_strictAnti₀ (toReal_pos hq₀ hpq.ne_top) (toReal_strict_mono hp_top hpq)
  · apply Eventually.of_forall
    simp only [iSup_le_iff]
    refine fun ε s hs ↦ (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq.le
      (hf.1.mono_measure μ.restrict_le_self)).trans ?_
    simp only [MeasurableSet.univ, Measure.restrict_apply, univ_inter, one_div]
    apply mul_le_mul' (eLpNorm_mono_measure f μ.restrict_le_self) (rpow_le_rpow hs _)
    rw [sub_nonneg]
    rcases eq_or_ne p ∞ with rfl | hp_top
    · simp
    · exact inv_anti₀ (toReal_pos hq₀ hpq.ne_top) (toReal_mono hp_top hpq.le)

theorem MemLp.tendsto_iSup_eLpNorm_restrict_nhds_zero_of_ne_top (hp : p ≠ ∞) (hf : MemLp f p μ) :
    Tendsto (fun ε ↦ ⨆ (s : Set α) (_ : μ s ≤ ε), eLpNorm f p (μ.restrict s)) (𝓝 0) (𝓝 0) := by
  rcases eq_or_ne p 0 with rfl | hp₀
  · simp
  apply (nhds_zero_basis.tendsto_iff nhds_zero_basis_Iic).2 fun ε hε ↦ ?_
  simp only [mem_Iio, mem_Iic, iSup_le_iff]
  have hfp := hf.2
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp, rpow_lt_top_iff_of_pos] at hfp; swap
  · simp [toReal_pos hp₀ hp]
  obtain ⟨δ, hδ, hδf⟩ := exists_pos_setLIntegral_lt_of_measure_lt hfp.ne
    (rpow_pos_of_nonneg hε p.toReal_nonneg).ne'
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp]
  refine ⟨δ, hδ, fun γ hγ s hs ↦ ?_⟩
  replace hδf := (hδf s (hs.trans_lt hγ)).le
  rwa [one_div, rpow_inv_le_iff (toReal_pos hp₀ hp)]

theorem MemLp.tendsto_iSup_eLpNorm_restrict_nhds_zero (hq : q ≠ ∞) (hp : q ≤ p) (hf : MemLp f p μ) :
    Tendsto (fun ε ↦ ⨆ (s : Set α) (_ : μ s ≤ ε), eLpNorm f q (μ.restrict s)) (𝓝 0) (𝓝 0) := by
  rcases eq_or_ne p q with rfl | h
  · exact hf.tendsto_iSup_eLpNorm_restrict_nhds_zero_of_ne_top hq
  · exact hf.tendsto_iSup_eLpNorm_restrict_nhds_zero_of_lt (h.symm.lt_of_le hp)

theorem MemLp.tendsto_iSup_eLpNorm_restrict_nhds_zero' (hp : p ≠ ∞) (hf : MemLp f p μ) :
    Tendsto (fun ε ↦ ⨆ (s : Set α) (_ : μ s ≤ ε), eLpNorm f p (μ.restrict s)) (𝓝 0) (𝓝 0) :=
  hf.tendsto_iSup_eLpNorm_restrict_nhds_zero hp le_rfl

@[deprecated "This lemma is superseded by `MemLp.tendsto_iSup_eLpNorm_restrict_nhds_zero''`"
  (since := "2026-08-17")]
theorem MemLp.tendsto_eLpNorm_restrict_zero (_hp_one : 1 ≤ p) (hp_top : p ≠ ∞) (hf : MemLp f p μ) :
    Tendsto (fun ε ↦ ⨆ (s : Set α) (_ : μ s ≤ ε), eLpNorm f p (μ.restrict s)) (𝓝 0) (𝓝 0) :=
  hf.tendsto_iSup_eLpNorm_restrict_nhds_zero hp_top le_rfl

theorem MemLp.tendsto_eLpNorm_restrict_nhds_zero {l : Filter ι} {s : ι → Set α} (hq : q ≠ ∞)
    (hp : q ≤ p) (hf : MemLp f p μ) (hs : Tendsto (fun i ↦ μ (s i)) l (𝓝 0)) :
    Tendsto (fun i ↦ eLpNorm f q (μ.restrict (s i))) l (𝓝 0) := by
  refine nhds_zero_basis_Iic.tendsto_right_iff.2 fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hδf⟩ := (nhds_zero_basis_Iic.tendsto_iff nhds_zero_basis_Iic).1
    (hf.tendsto_iSup_eLpNorm_restrict_nhds_zero hq hp) ε hε
  filter_upwards [nhds_zero_basis_Iic.tendsto_right_iff.1 hs δ hδ] with i hi
  simp only [mem_Iic, iSup_le_iff] at hδf hi ⊢
  exact hδf (μ (s i)) hi (s i) le_rfl

theorem MemLp.eLpNormEssSup_restrict_norm_ge (hf : MemLp f ∞ μ) :
    ∀ᶠ M in 𝓝 ∞, eLpNormEssSup f (μ.restrict { x | M ≤ ‖f x‖ₑ }) = 0 := by
  filter_upwards [MemLp.restrict_norm_ge_eq_zero hf] with M hM
  simp [hM]

theorem MemLp.tendsto_measure_norm_ge (hp : p ≠ 0) (hf : MemLp f p μ) :
    Tendsto (fun M ↦ μ { x | M ≤ ‖f x‖ₑ }) (𝓝 ∞) (𝓝 0) := by
  rcases eq_top_or_lt_top p with rfl | hp'
  · apply EventuallyEq.tendsto
    filter_upwards [MemLp.restrict_norm_ge_eq_zero hf] with M hM
    simp [μ.restrict_eq_zero.1 hM]
  have hf' : eLpNorm f p μ ^ p.toReal ≠ ∞ := rpow_ne_top_of_nonneg toReal_nonneg hf.2.ne
  have hpr : 0 < p.toReal := toReal_pos hp hp'.ne
  apply tendsto_nhds_bot_mono (f := fun M ↦ eLpNorm f p μ ^ p.toReal / M ^ p.toReal)
  · rw [bot_eq_zero, ← div_top (a := eLpNorm f p μ ^ p.toReal)]
    exact Tendsto.const_div (tendsto_rpow_at_top hpr) (.inr hf')
  · refine _root_.nhds_top_basis.eventually_iff.2 ⟨0, zero_lt_top, fun M hM ↦ ?_⟩
    simp only
    apply (ENNReal.le_div_iff_mul_le (.inl (rpow_pos_of_nonneg hM hpr.le).ne') (.inr hf')).2
    rw [mul_comm, ← rpow_le_rpow_iff (inv_pos.2 hpr),
      mul_rpow_of_nonneg _ _ (inv_nonneg.2 hpr.le), ← rpow_mul, ← rpow_mul,
      mul_inv_cancel₀ hpr.ne', rpow_one, rpow_one, ← one_div]
    apply le_eLpNorm_of_bddBelow' hp hp'.ne M (nullMeasurableSet_le aemeasurable_const hf.1.enorm)
    exact Eventually.of_forall (by simp)

theorem MemLp.tendsto_eLpNorm_norm_ge_of_le (hq : q ≤ p) (hf : MemLp f p μ) :
    Tendsto (fun M ↦ eLpNorm f q (μ.restrict { x | M ≤ ‖f x‖ₑ })) (𝓝 ∞) (𝓝 0) := by
  rcases eq_or_ne q ∞ with rfl | hq'
  · rw [top_unique hq] at hf
    apply EventuallyEq.tendsto
    filter_upwards [MemLp.restrict_norm_ge_eq_zero hf] with M hM
    simp [hM]
  rcases eq_or_ne p 0 with rfl | hp
  · simp [bot_unique hq]
  exact hf.tendsto_eLpNorm_restrict_nhds_zero hq' hq (hf.tendsto_measure_norm_ge hp)

theorem MemLp.tendsto_eLpNorm_norm_ge (hf : MemLp f p μ) :
    Tendsto (fun M ↦ eLpNorm f p (μ.restrict { x | M ≤ ‖f x‖ₑ })) (𝓝 ∞) (𝓝 0) :=
  hf.tendsto_eLpNorm_norm_ge_of_le le_rfl

theorem tendsto_indicator_ge (f : α → β) (x : α) :
    Tendsto (fun M : ℕ => { x | (M : ℝ) ≤ ‖f x‖₊ }.indicator f x) atTop (𝓝 0) := by
  refine tendsto_atTop_of_eventually_const (i₀ := Nat.ceil (‖f x‖₊ : ℝ) + 1) fun n hn => ?_
  rw [Set.indicator_of_notMem]
  simp only [not_le, Set.mem_ofPred_eq]
  refine lt_of_le_of_lt (Nat.le_ceil _) ?_
  refine lt_of_lt_of_le (lt_add_one _) ?_
  norm_cast

theorem MemLp.integral_indicator_norm_ge_nonneg_le (hf : MemLp f 1 μ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ (∫⁻ x, ‖{ x | M ≤ ‖f x‖₊ }.indicator f x‖ₑ ∂μ) ≤ ε := by
  obtain ⟨M, hM_top, hM⟩ := (nhds_top_basis_Ici.tendsto_iff nhds_zero_basis).1
    hf.tendsto_eLpNorm_norm_ge ε hε
  refine ⟨M.toReal, toReal_nonneg, ?_⟩
  simp only [mem_Ici, mem_Iio, coe_nnnorm, enorm_indicator_eq_indicator_enorm,
    eLpNorm_one_eq_lintegral_enorm] at hM ⊢
  apply (lintegral_indicator_le _ _).trans
  apply (hM M le_rfl).le.trans'
  refine lintegral_mono_set fun x hx ↦ ?_
  simp only [mem_ofPred_eq] at hx ⊢
  replace hx := ofReal_le_ofReal hx
  rwa [ENNReal.ofReal_toReal hM_top.ne, ofReal_norm] at hx

@[deprecated "This lemma is weaker than `MeasureTheory.MemLp.integral_indicator_norm_ge_nonneg_le`
  as the latter provides `0 ≤ M` and does not require the measurability of `f`."
  (since := "2026-08-16")]
theorem MemLp.integral_indicator_norm_ge_le (hf : MemLp f 1 μ) (_hmeas : StronglyMeasurable f)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ M : ℝ, (∫⁻ x, ‖{ x | M ≤ ‖f x‖₊ }.indicator f x‖₊ ∂μ) ≤ ε := by
  obtain ⟨M, hM_top, hM⟩ := hf.integral_indicator_norm_ge_nonneg_le hε
  exact ⟨M, hM⟩

@[deprecated "This lemma is superseded by `MeasureTheory.MemLp.integral_indicator_norm_ge_nonneg_le`
which does not require measurability." (since := "2026-08-16")]
theorem MemLp.integral_indicator_norm_ge_nonneg_le_of_meas (hf : MemLp f 1 μ)
    (_hmeas : StronglyMeasurable f) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ (∫⁻ x, ‖{ x | M ≤ ‖f x‖₊ }.indicator f x‖ₑ ∂μ) ≤ ε :=
  hf.integral_indicator_norm_ge_nonneg_le hε

theorem MemLp.eLpNormEssSup_indicator_norm_ge_eq_zero (hf : MemLp f ∞ μ) :
    ∃ M : ℝ, eLpNormEssSup ({ x | M ≤ ‖f x‖₊ }.indicator f) μ = 0 := by
  obtain ⟨M, hM_top, hM⟩ := nhds_top_basis_Ici.eventually_iff.1 hf.eLpNormEssSup_restrict_norm_ge
  use M.toReal
  simp only [mem_Ici, eLpNormEssSup_eq_zero_iff, coe_nnnorm] at hM ⊢
  filter_upwards [ae_imp_of_ae_restrict (hM le_rfl)] with x hx
  simp only [Pi.zero_apply, indicator_apply_eq_zero, mem_ofPred_eq] at hx ⊢
  refine fun h ↦ hx ?_
  replace h := ofReal_le_ofReal h
  rwa [ENNReal.ofReal_toReal hM_top.ne, ofReal_norm] at h

/-- This lemma implies that a single function is uniformly integrable (in the probability sense). -/
theorem MemLp.eLpNorm_indicator_norm_ge_pos_le (hf : MemLp f p μ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ eLpNorm ({ x | M ≤ ‖f x‖₊ }.indicator f) p μ ≤ ε := by
  obtain ⟨M, hM_top, hM⟩ := (nhds_top_basis_Ici.tendsto_iff nhds_zero_basis_Iic).1
    hf.tendsto_eLpNorm_norm_ge ε hε
  refine ⟨max M.toReal 1, by simp, ?_⟩
  specialize hM (max M 1) (le_max_left M 1)
  have hmeas : NullMeasurableSet { x | max M 1 ≤ ‖f x‖ₑ } μ :=
    nullMeasurableSet_le aemeasurable_const hf.enorm.1.aemeasurable
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hmeas] at hM
  simp only [sup_le_iff, mem_Iic, coe_nnnorm] at hM ⊢
  apply le_of_eq_of_le _ hM
  congr 3
  ext x
  simp [← ofReal_le_ofReal_iff (norm_nonneg (f x)), ofReal_toReal hM_top.ne]

@[deprecated "This lemma is slightly weaker than
`MeasureTheory.MemLp.eLpNorm_indicator_norm_ge_pos_le` as the latter provides `0 < M`."
(since := "2026-08-16")]
theorem MemLp.eLpNorm_indicator_norm_ge_le (hf : MemLp f p μ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ M : ℝ, eLpNorm ({ x | M ≤ ‖f x‖₊ }.indicator f) p μ ≤ ε := by
  obtain ⟨M, _, hM⟩ := hf.eLpNorm_indicator_norm_ge_pos_le hε
  exact ⟨M, hM⟩

end

theorem eLpNorm_indicator_le_of_bound {f : α → β} (hp_top : p ≠ ∞) {ε : ℝ≥0∞} (hε : 0 < ε) {M : ℝ}
    (hf : ∀ x, ‖f x‖ < M) :
    ∃ δ > 0, ∀ s, NullMeasurableSet s μ → μ s ≤ δ → eLpNorm (s.indicator f) p μ ≤ ε := by
  by_cases! hM : M ≤ 0
  · refine ⟨1, zero_lt_one, fun s _ _ => ?_⟩
    rw [(_ : f = 0)]
    · simp
    · ext x
      rw [Pi.zero_apply, ← norm_le_zero_iff]
      exact (lt_of_lt_of_le (hf x) hM).le
  refine ⟨(ε / ENNReal.ofReal M) ^ p.toReal,
    rpow_pos_of_nonneg (ENNReal.div_pos hε.ne' coe_ne_top) toReal_nonneg, ?_⟩
  intro s hs hμ
  rcases eq_zero_or_pos p with rfl | hp
  · simp
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  have haebdd : ∀ᵐ x ∂μ.restrict s, ‖f x‖ ≤ M := by
    filter_upwards
    exact fun x ↦ (hf x).le
  refine (eLpNorm_le_of_ae_bound haebdd).trans ?_
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    ← ENNReal.le_div_iff_mul_le (.inl _) (.inl ofReal_ne_top)]
  · rwa [rpow_inv_le_iff (toReal_pos hp.ne' hp_top)]
  · simpa only [ofReal_eq_zero, not_le, Ne]

section

variable {f : α → β}

theorem MemLp.eLpNorm_indicator_le (hp : p ≠ ∞) (hf : MemLp f p μ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s, NullMeasurableSet s μ → μ s ≤ δ → eLpNorm (s.indicator f) p μ ≤ ε := by
  have key := hf.tendsto_iSup_eLpNorm_restrict_nhds_zero' hp
  simp only [nhds_zero_basis_Iic.tendsto_iff nhds_zero_basis_Iic, mem_Iic, iSup_le_iff] at key
  obtain ⟨δ, hδ, hδf⟩ := key ε hε
  refine ⟨δ, hδ, fun s hs hsμ ↦ ?_⟩
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  exact hδf δ le_rfl s hsμ

@[deprecated "This lemma is superseded by `MeasureTheory.MemLp.eLpNorm_indicator_le` which does
not require measurability on `f`." (since := "2026-08-17")]
theorem MemLp.eLpNorm_indicator_le_of_meas (_hp_one : 1 ≤ p) (hp_top : p ≠ ∞) (hf : MemLp f p μ)
    (_hmeas : StronglyMeasurable f) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s, NullMeasurableSet s μ → μ s ≤ δ → eLpNorm (s.indicator f) p μ ≤ ε :=
  hf.eLpNorm_indicator_le hp_top hε

@[deprecated "Auxiliary lemma for `MeasureTheory.MemLp.eLpNorm_indicator_le`."
(since := "2026-08-17")]
theorem MemLp.eLpNorm_indicator_le' (_hp_one : 1 ≤ p) (hp_top : p ≠ ∞) (hf : MemLp f p μ)
    (_hmeas : StronglyMeasurable f) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s, NullMeasurableSet s μ → μ s ≤ δ → eLpNorm (s.indicator f) p μ ≤ 2 * ε :=
  hf.eLpNorm_indicator_le hp_top (by positivity)

/-- A constant function is uniformly integrable. -/
theorem unifIntegrable_const {g : α → β} (hp : p ≠ ∞) (hg : MemLp g p μ) :
    UnifIntegrable (fun _ : ι ↦ g) p μ := by
  rcases isEmpty_or_nonempty ι with _ | _
  · exact unifIntegrable_of_isEmpty
  rw [UnifIntegrable]
  simp only [ciSup_const]
  exact hg.tendsto_iSup_eLpNorm_restrict_nhds_zero' hp

/-- A single function is uniformly integrable. -/
theorem unifIntegrable_subsingleton [Subsingleton ι] (hp : p ≠ ∞)
    {f : ι → α → β} (hf : ∀ i, MemLp (f i) p μ) : UnifIntegrable f p μ := by
  rcases isEmpty_or_nonempty ι with _ | ⟨⟨i⟩⟩
  · exact unifIntegrable_of_isEmpty
  rw [UnifIntegrable]
  simp only [ciSup_subsingleton i]
  exact (hf i).tendsto_iSup_eLpNorm_restrict_nhds_zero' hp

/-- A finite sequence of Lp functions is uniformly integrable. -/
theorem unifIntegrable_finite [Finite ι] (hp : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, MemLp (f i) p μ) : UnifIntegrable f p μ := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ ?_
  have key := fun i ↦ (hf i).tendsto_iSup_eLpNorm_restrict_nhds_zero' hp
  simp only [ENNReal.tendsto_nhds_zero] at key
  filter_upwards [eventually_all.2 (fun i ↦ key i ε hε)] with a ha
  exact iSup_le ha

@[deprecated (since := "2026-07-24")] alias unifIntegrable_fin := unifIntegrable_finite

end
variable {f : ℕ → α → β} {g : α → β}

/-- A sequence of uniformly integrable functions which converges μ-a.e. converges in Lp. -/
theorem tendsto_Lp_finite_of_tendsto_ae_of_meas [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g) (hg' : MemLp g p μ)
    (hui : UnifIntegrable f p μ) (hfg : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  rcases eq_top_or_lt_top ε with rfl | h
  · simp
  by_cases hμ : μ = 0
  · simp [hμ]
  have hε' : 0 < ε / 3 := ε.div_pos hε.ne' ofNat_ne_top
  have hdivp : 0 ≤ 1 / p.toReal := by positivity
  have hpow : 0 < measureUnivNNReal μ ^ (1 / p.toReal) :=
    Real.rpow_pos_of_pos (measureUnivNNReal_pos hμ) _
  obtain ⟨δ₁, hδ₁, heLpNorm₁⟩ := unifIntegrable_iff.1 hui (ε / 3) hε'
  obtain ⟨δ₂, hδ₂, heLpNorm₂⟩ := hg'.eLpNorm_indicator_le hp' hε'
  obtain ⟨t, htm, ht₁, ht₂⟩ := tendstoUniformlyOn_of_ae_tendsto' hf hg hfg (lt_min hδ₁ hδ₂)
  rw [Metric.tendstoUniformlyOn_iff] at ht₂
  specialize ht₂ (ε.toReal / (3 * measureUnivNNReal μ ^ (1 / p.toReal)))
    (div_pos (toReal_pos (gt_iff_lt.1 hε).ne' h.ne) (mul_pos (by simp) hpow))
  obtain ⟨N, hN⟩ := eventually_atTop.1 ht₂; clear ht₂
  refine ⟨N, fun n hn => ?_⟩
  rw [← t.indicator_self_add_compl (f n - g)]
  grw [eLpNorm_add_le (((hf n).sub hg).indicator htm).aestronglyMeasurable
    (((hf n).sub hg).indicator htm.compl).aestronglyMeasurable hp, sub_eq_add_neg,
    Set.indicator_add' t, Set.indicator_neg', eLpNorm_add_le
    ((hf n).indicator htm).aestronglyMeasurable (hg.indicator htm).neg.aestronglyMeasurable hp]
  have hnf : eLpNorm (t.indicator (f n)) p μ ≤ ε / 3 := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict htm.nullMeasurableSet]
    exact heLpNorm₁ n t (ht₁.trans (min_le_left _ _))
  have hng : eLpNorm (t.indicator g) p μ ≤ ε / 3 :=
    heLpNorm₂ t htm.nullMeasurableSet (ht₁.trans (min_le_right _ _))
  have hlt : eLpNorm (tᶜ.indicator (f n - g)) p μ ≤ ε / 3 := by
    specialize hN n hn
    have : 0 ≤ ε.toReal / (3 * measureUnivNNReal μ ^ (1 / p.toReal)) := by positivity
    have hε₃ : ENNReal.ofReal (ε.toReal / 3) = ε / 3 := by
      rw [ofReal_div_of_pos (show (0 : ℝ) < 3 by simp), ofReal_toReal h.ne]
      simp
    have := eLpNorm_indicator_sub_le_of_dist_bdd μ hp' htm.compl this fun x hx =>
      (dist_comm (g x) (f n x) ▸ (hN x hx).le :
        dist (f n x) (g x) ≤ ε.toReal / (3 * measureUnivNNReal μ ^ (1 / p.toReal)))
    refine this.trans ?_
    rw [div_mul_eq_div_mul_one_div, ← ofReal_toReal (measure_lt_top μ tᶜ).ne,
      ofReal_rpow_of_nonneg toReal_nonneg hdivp, ← ofReal_mul, mul_assoc]; swap
    · positivity
    rw [ofReal_mul (by positivity), hε₃]
    refine mul_le_of_le_one_right (by positivity) (ofReal_le_one.2 ?_)
    rw [mul_comm, mul_one_div, div_le_one]
    · gcongr
      refine (toReal_le_of_le_ofReal (measureUnivNNReal_pos hμ).le ?_)
      rw [ofReal_coe_nnreal, coe_measureUnivNNReal]
      exact measure_mono (Set.subset_univ _)
    · exact Real.rpow_pos_of_pos (measureUnivNNReal_pos hμ) _
  rw [eLpNorm_neg, ← add_thirds ε, ← sub_eq_add_neg]
  gcongr

/-- A sequence of uniformly integrable functions which converges μ-a.e. converges in Lp. -/
theorem tendsto_Lp_finite_of_tendsto_ae [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : MemLp g p μ) (hui : UnifIntegrable f p μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  have : ∀ n, eLpNorm (f n - g) p μ = eLpNorm ((hf n).mk (f n) - hg.1.mk g) p μ :=
    fun n => eLpNorm_congr_ae ((hf n).ae_eq_mk.sub hg.1.ae_eq_mk)
  simp_rw [this]
  refine tendsto_Lp_finite_of_tendsto_ae_of_meas hp hp' (fun n => (hf n).stronglyMeasurable_mk)
    hg.1.stronglyMeasurable_mk (hg.ae_eq hg.1.ae_eq_mk) (hui.ae_eq fun n => (hf n).ae_eq_mk) ?_
  have h_ae_forall_eq : ∀ᵐ x ∂μ, ∀ n, f n x = (hf n).mk (f n) x := by
    rw [ae_all_iff]
    exact fun n => (hf n).ae_eq_mk
  filter_upwards [hfg, h_ae_forall_eq, hg.1.ae_eq_mk] with x hx_tendsto hxf_eq hxg_eq
  rw [← hxg_eq]
  convert! hx_tendsto using 1
  ext1 n
  exact (hxf_eq n).symm

theorem unifIntegrable_of_tendsto_Lp_zero (hp : p ≠ ∞) (hf : ∀ n, MemLp (f n) p μ)
    (hf_tendsto : Tendsto (fun n ↦ eLpNorm (f n) p μ) atTop (𝓝 0)) : UnifIntegrable f p μ := by
  apply unifIntegrable_iff.2 fun ε hε ↦ ?_
  rw [ENNReal.tendsto_atTop_zero] at hf_tendsto
  obtain ⟨N, hN⟩ := hf_tendsto (ε) (by simpa)
  let F : Fin N → α → β := fun n ↦ f n
  have hF : ∀ n, MemLp (F n) p μ := fun n => hf n
  obtain ⟨δ₁, hδpos₁, hδ₁⟩ := unifIntegrable_iff.1 (unifIntegrable_finite hp hF) ε hε
  refine ⟨δ₁, hδpos₁, fun n s hμs ↦ ?_⟩
  by_cases! hn : n < N
  · exact hδ₁ ⟨n, hn⟩ s hμs
  · exact (eLpNorm_restrict_le (f n) p μ s).trans (hN n hn)

/-- Convergence in Lp implies uniform integrability. -/
theorem unifIntegrable_of_tendsto_Lp (hp : p ≠ ∞) (hf : ∀ n, MemLp (f n) p μ)
    (hg : MemLp g p μ) (hfg : Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0)) :
    UnifIntegrable f p μ := by
  have : f = (fun _ => g) + fun n => f n - g := by ext1 n; simp
  rw [this]
  refine UnifIntegrable.add ?_ ?_ (fun _ ↦ hg.1) fun n ↦ (hf n).1.sub hg.1
  · exact unifIntegrable_const hp hg
  · exact unifIntegrable_of_tendsto_Lp_zero hp (fun n ↦ (hf n).sub hg) hfg

/-- Forward direction of Vitali's convergence theorem: if `f` is a sequence of uniformly integrable
functions that converge in measure to some function `g` in a finite measure space, then `f`
converge in Lp to `g`. -/
theorem tendsto_Lp_finite_of_tendstoInMeasure [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : MemLp g p μ) (hui : UnifIntegrable f p μ)
    (hfg : TendstoInMeasure μ f atTop g) : Tendsto (fun n ↦ eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, _, hms'⟩ := TendstoInMeasure.exists_seq_tendsto_ae fun ε hε => (hfg ε hε).comp hns
  exact ⟨ms, tendsto_Lp_finite_of_tendsto_ae hp hp' (fun _ ↦ hf _) hg (hui.comp _) hms'⟩

/-- **Vitali's convergence theorem**: A sequence of functions `f` converges to `g` in Lp if and
only if it is uniformly integrable and converges to `g` in measure. -/
theorem tendstoInMeasure_iff_tendsto_Lp_finite [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ n, MemLp (f n) p μ) (hg : MemLp g p μ) :
    TendstoInMeasure μ f atTop g ∧ UnifIntegrable f p μ ↔
      Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) :=
  ⟨fun h => tendsto_Lp_finite_of_tendstoInMeasure hp hp' (fun n => (hf n).1) hg h.2 h.1, fun h =>
    ⟨tendstoInMeasure_of_tendsto_eLpNorm (lt_of_lt_of_le zero_lt_one hp).ne'
        (fun n => (hf n).aestronglyMeasurable) hg.aestronglyMeasurable h,
      unifIntegrable_of_tendsto_Lp hp' hf hg h⟩⟩

theorem unifIntegrable_of_nnreal (hp : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (h : ∀ ε > 0, ∃ M : ℝ≥0, ∀ i, eLpNorm ({ x | M ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ε) :
    UnifIntegrable f p μ :=
  ((unifLpTail_iff_nnreal hf).2 h).unifIntegrable hp hf

@[deprecated "This lemma is superseded by `unifIntegrable_of_nnreal` which do not require `C`
to be positive." (since := "2026-08-17")]
theorem unifIntegrable_of' (_hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, StronglyMeasurable (f i))
    (h : ∀ ε > 0, ∃ C : ℝ≥0, 0 < C ∧
      ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ε) :
    UnifIntegrable f p μ := by
  apply unifIntegrable_of_nnreal hp' (fun i ↦ (hf i).aestronglyMeasurable) fun ε hε ↦ ?_
  obtain ⟨C, _, hC⟩ := h ε hε
  exact ⟨C, hC⟩

/-- If `fn` is `UnifIntegrable`, then the family of limits in probability of sequences of `fn` is
`UnifIntegrable`. -/
lemma UnifIntegrable.unifIntegrable_of_tendstoInMeasure {κ : Type*} (u : Filter κ) [NeBot u]
    [IsCountablyGenerated u] {fn : ι → α → β} (hUI : UnifIntegrable fn p μ)
    (hfn : ∀ i, AEStronglyMeasurable (fn i) μ) :
    UnifIntegrable (fun (f : {g : α → β | ∃ ni : κ → ι,
      TendstoInMeasure μ (fn ∘ ni) u g}) ↦ f.1) p μ := by
  refine unifIntegrable_iff'.2 fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hδ'⟩ := (unifIntegrable_iff.1 hUI) ε hε
  refine ⟨δ, hδ, fun ⟨f, s, hs⟩ t ht ht' ↦ ?_⟩
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict ht.nullMeasurableSet]
  apply eLpNorm_le_of_tendstoInMeasure _ (hs.indicator t) (fun n ↦ (hfn (s n)).indicator ht)
  apply Eventually.of_forall fun n ↦ ?_
  rw [eLpNorm_indicator_eq_eLpNorm_restrict ht.nullMeasurableSet, Function.comp_apply]
  exact hδ' (s n) t ht'

/-- If `fn` is `UnifIntegrable`, then the family of a.e. limits of sequences of `fn` is
`UnifIntegrable`. -/
lemma UnifIntegrable.unifIntegrable_of_ae_tendsto {κ : Type*} (u : Filter κ) [NeBot u]
    [IsCountablyGenerated u] {fn : ι → α → β} (hUI : UnifIntegrable fn p μ)
    (hfn : ∀ i, AEStronglyMeasurable (fn i) μ) :
    UnifIntegrable (fun (f : {g : α → β | ∃ ni : κ → ι,
      ∀ᵐ (x : α) ∂μ, Tendsto (fun n ↦ fn (ni n) x) u (𝓝 (g x))}) ↦ f.1) p μ := by
  refine unifIntegrable_iff'.2 fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hδ'⟩ := (unifIntegrable_iff.1 hUI) ε hε
  refine ⟨δ, hδ, fun ⟨f, s, hs⟩ t ht hμt ↦ ?_⟩
  refine Lp.eLpNorm_le_of_ae_tendsto
    (Eventually.of_forall (f := u) fun n ↦ hδ' (s n) t hμt) ?_ ?_
  · exact fun n ↦ (hfn (s n)).mono_measure μ.restrict_le_self
  · exact hs.filter_mono ae_restrict_le

section UniformIntegrable

/-! `UniformIntegrable`

In probability theory, uniform integrability normally refers to the condition that a sequence
of function `(fₙ)` satisfies for all `ε > 0`, there exists some `C ≥ 0` such that
`∫ x in {|fₙ| ≥ C}, fₙ x ∂μ ≤ ε` for all `n`.

In this section, we will develop some API for `UniformIntegrable` and prove that
`UniformIntegrable` is equivalent to this definition of uniform integrability.
-/

variable {p : ℝ≥0∞} {f : ι → α → β}



/-- A finite sequence of Lp functions is uniformly integrable in the probability sense. -/
theorem uniformIntegrable_finite [Finite ι] (hp : p ≠ ∞)
    (hf : ∀ i, MemLp (f i) p μ) : UniformIntegrable f p μ := by
  refine ⟨fun n ↦ (hf n).1, unifIntegrable_finite hp hf, ?_⟩
  rcases isEmpty_or_nonempty ι with _ | ⟨⟨i⟩⟩
  · simp
  rw [← iSup_univ, finite_univ.ciSup_lt_iff ⟨i, mem_univ i, by simp⟩]
  exact fun i _ ↦ (hf i).2

/-- A single function is uniformly integrable in the probability sense. -/
theorem uniformIntegrable_subsingleton [Subsingleton ι] (hp : p ≠ ∞)
    (hf : ∀ i, MemLp (f i) p μ) : UniformIntegrable f p μ :=
  uniformIntegrable_finite hp hf

/-- A constant sequence of functions is uniformly integrable in the probability sense. -/
theorem uniformIntegrable_const {g : α → β} (hp : p ≠ ∞) (hg : MemLp g p μ) :
    UniformIntegrable (fun _ : ι ↦ g) p μ := by
  rcases isEmpty_or_nonempty ι
  · simp
  exact ⟨fun _ ↦ hg.1, unifIntegrable_const hp hg, by simp [hg.2]⟩

/-- A sequence of functions `(fₙ)` is uniformly integrable in the probability sense if for all
`ε > 0`, there exists some `C` such that `∫ x in {|fₙ| ≥ C}, fₙ x ∂μ ≤ ε` for all `n`. -/
theorem uniformIntegrable_of_nnreal [IsFiniteMeasure μ] (hp : p ≠ ∞)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (h : ∀ ε > 0, ∃ C : ℝ≥0, ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ε) :
    UniformIntegrable f p μ :=
  ((unifLpTail_iff_nnreal hf).2 h).uniformIntegrable hp hf

@[deprecated "This lemma is superseded by `uniformIntegrable_of_nnreal` which only requires
`AEStronglyMeasurable`." (since := "2026-08-17")]
theorem uniformIntegrable_of' [IsFiniteMeasure μ] (_hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ i, StronglyMeasurable (f i))
    (h : ∀ ε > 0, ∃ C : ℝ≥0, ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ε) :
    UniformIntegrable f p μ :=
  uniformIntegrable_of_nnreal hp' (fun i ↦ (hf i).aestronglyMeasurable) h

theorem UniformIntegrable.spec (hfu : UniformIntegrable f p μ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ M : ℝ≥0, ∀ i, eLpNorm ({ x | M ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ε :=
  (unifLpTail_iff_nnreal hfu.1).1 hfu.unifLpTail ε hε

@[deprecated "This lemma is superseded by `UniformIntegrable.spec` which does not require
measurability." (since := "2026-08-18")]
theorem UniformIntegrable.spec' (_hp : p ≠ 0) (_hp' : p ≠ ∞)
    (_hf : ∀ i, AEStronglyMeasurable (f i) μ) (hfu : UniformIntegrable f p μ) {ε : ℝ≥0∞}
    (hε : 0 < ε) :
    ∃ M : ℝ≥0, ∀ i, eLpNorm ({ x | M ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ε :=
  hfu.spec hε

/-- The definition of uniform integrable in mathlib is equivalent to the definition commonly
found in literature. -/
theorem uniformIntegrable_iff [IsFiniteMeasure μ] (hp : p ≠ ∞) :
    UniformIntegrable f p μ ↔ (∀ i, AEStronglyMeasurable (f i) μ) ∧
        ∀ ε > 0, ∃ C : ℝ≥0, ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ε :=
  ⟨fun h ↦ ⟨h.1, fun _ ↦ h.spec⟩, fun h ↦ uniformIntegrable_of_nnreal hp h.1 h.2⟩

/-- The averaging of a uniformly integrable sequence is also uniformly integrable. -/
theorem uniformIntegrable_average
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hp : 1 ≤ p) {f : ℕ → α → E} (hf : UniformIntegrable f p μ) :
    UniformIntegrable (fun (n : ℕ) => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, f i)) p μ := by
  obtain ⟨hf₁, hf₂, hf₃⟩ := hf
  refine ⟨fun n ↦ ?_, unifIntegrable_iff'.2 fun ε hε ↦ ?_, ?_⟩
  · exact (Finset.aestronglyMeasurable_sum _ fun i _ => hf₁ i).const_smul _
  · obtain ⟨δ, hδ₁, hδ₂⟩ := (unifIntegrable_iff.1 hf₂) ε hε
    refine ⟨δ, hδ₁, fun n s hs hle ↦ ?_⟩
    simp_rw [Finset.smul_sum]
    refine (eLpNorm_sum_le (fun i _ ↦ ((hf₁ i).const_smul _).mono_measure
      μ.restrict_le_self) hp).trans ?_
    have this i : s.indicator ((n : ℝ)⁻¹ • f i) = (↑n : ℝ)⁻¹ • s.indicator (f i) :=
      indicator_const_smul _ _ _
    obtain rfl | hn := eq_or_ne n 0
    · simp
    simp_rw [eLpNorm_const_smul, ← Finset.mul_sum]
    rw [enorm_inv (by positivity), Real.enorm_natCast, ← ENNReal.div_eq_inv_mul]
    refine div_le_of_le_mul' ?_
    have key := Finset.sum_le_card_nsmul (.range n) (fun i ↦ eLpNorm (f i) p (μ.restrict s)) ε
    simp only [Finset.mem_range, Finset.card_range, nsmul_eq_mul] at key
    exact key fun i _ ↦ hδ₂ i s hle
  · refine hf₃.trans_le' (iSup_le fun n ↦ ?_)
    simp_rw [Finset.smul_sum]
    apply (eLpNorm_sum_le (fun i _ ↦ (hf₁ i).const_smul _) hp).trans
    obtain rfl | hn := eq_or_ne n 0
    · simp
    simp_rw [eLpNorm_const_smul, ← Finset.mul_sum]
    rw [enorm_inv (by positivity), Real.enorm_natCast, ← ENNReal.div_eq_inv_mul]
    refine div_le_of_le_mul' ?_
    apply (Finset.sum_le_card_nsmul (.range n) _ _ (fun i _ ↦ le_iSup _ i)).trans
    simp

/-- The averaging of a uniformly integrable real-valued sequence is also uniformly integrable. -/
theorem uniformIntegrable_average_real (hp : 1 ≤ p) {f : ℕ → α → ℝ} (hf : UniformIntegrable f p μ) :
    UniformIntegrable (fun n => (∑ i ∈ Finset.range n, f i) / (n : α → ℝ)) p μ := by
  convert! uniformIntegrable_average hp hf using 2 with n
  ext x
  simp [div_eq_inv_mul]

/-- If `fn` is `UniformIntegrable`, then the family of limits in probability of sequences of `fn` is
`UniformIntegrable`. -/
lemma UniformIntegrable.uniformIntegrable_of_tendstoInMeasure {κ : Type*} (u : Filter κ) [NeBot u]
    [IsCountablyGenerated u] {fn : ι → α → β} (hUI : UniformIntegrable fn p μ) :
    UniformIntegrable (fun (f : {g : α → β | ∃ ni : κ → ι,
      TendstoInMeasure μ (fn ∘ ni) u g}) ↦ f.1) p μ := by
  refine ⟨fun ⟨f, s, hs⟩ ↦ hs.aestronglyMeasurable (fun n ↦ hUI.aestronglyMeasurable (s n)), ?_, ?_⟩
  · exact hUI.unifIntegrable.unifIntegrable_of_tendstoInMeasure u hUI.aestronglyMeasurable
  · refine hUI.bdd.trans_le' (iSup_le fun ⟨f, s, hs⟩ ↦ ?_)
    refine eLpNorm_le_of_tendstoInMeasure (Eventually.of_forall fun i ↦ ?_) hs
      (fun n ↦ hUI.aestronglyMeasurable (s n))
    exact le_iSup (fun j ↦ eLpNorm (fn j) p μ) (s i)

/-- Suppose `f` is a sequence of functions that converges in measure to `g`. If `f` is
`UniformIntegrable`, then `g` is in `Lp`. -/
lemma UniformIntegrable.memLp_of_tendstoInMeasure {κ : Type*} {u : Filter κ} [NeBot u]
    [IsCountablyGenerated u] {f : κ → α → β} {g : α → β}
    (hUI : UniformIntegrable f p μ) (htends : TendstoInMeasure μ f u g) :
    MemLp g p μ := by
  simpa using (hUI.uniformIntegrable_of_tendstoInMeasure u).memLp ⟨g, ⟨fun n => n, htends⟩⟩

/-- Suppose `f` is a sequence of functions that converges in measure to `g`. If `f` is
`UniformIntegrable`, then `g` is integrable. -/
lemma UniformIntegrable.integrable_of_tendstoInMeasure {κ : Type*} {u : Filter κ} [NeBot u]
    [IsCountablyGenerated u] {f : κ → α → β} {g : α → β}
    (hUI : UniformIntegrable f 1 μ) (htends : TendstoInMeasure μ f u g) :
    Integrable g μ :=
  memLp_one_iff_integrable.mp (hUI.memLp_of_tendstoInMeasure htends)

/-- If `fn` is `UniformIntegrable`, then the family of a.e. limits of sequences of `fn` is
`UniformIntegrable`. -/
lemma UniformIntegrable.uniformIntegrable_of_ae_tendsto {κ : Type*} (u : Filter κ) [NeBot u]
    [IsCountablyGenerated u] {fn : ι → α → β}
    (hUI : UniformIntegrable fn p μ) :
    UniformIntegrable (fun (f : {g : α → β | ∃ ni : κ → ι,
      ∀ᵐ (x : α) ∂μ, Tendsto (fun n ↦ fn (ni n) x) u (𝓝 (g x))}) ↦ f.1) p μ := by
  refine ⟨fun ⟨f, s, hs⟩ ↦ aestronglyMeasurable_of_tendsto_ae u
    (fun n ↦ hUI.aestronglyMeasurable (s n)) hs, ?_, ?_⟩
  · exact hUI.unifIntegrable.unifIntegrable_of_ae_tendsto u hUI.aestronglyMeasurable
  · refine hUI.bdd.trans_le' (iSup_le fun ⟨f, s, hs⟩ ↦ ?_)
    apply Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall fun i ↦ ?_) (fun n ↦ hUI.1 (s n)) hs
    exact le_iSup (fun j ↦ eLpNorm (fn j) p μ) (s i)

/-- Suppose `f` is a sequence of functions that converges a.e. to `g`. If `f` is
`UniformIntegrable`, then `g` is in `Lp`. -/
lemma UniformIntegrable.memLp_of_ae_tendsto {κ : Type*} {u : Filter κ} [NeBot u]
    [IsCountablyGenerated u] {f : κ → α → β} {g : α → β} (hUI : UniformIntegrable f p μ)
    (htends : ∀ᵐ (x : α) ∂μ, Tendsto (fun n ↦ f n x) u (𝓝 (g x))) :
    MemLp g p μ := by
  simpa using (hUI.uniformIntegrable_of_ae_tendsto u).memLp ⟨g, ⟨fun n => n, htends⟩⟩

/-- Suppose `f` is a sequence of functions that converges a.e. to `g`. If `f` is
`UniformIntegrable`, then `g` is integrable. -/
lemma UniformIntegrable.integrable_of_ae_tendsto {κ : Type*} {u : Filter κ} [NeBot u]
    [IsCountablyGenerated u] {f : κ → α → β} {g : α → β} (hUI : UniformIntegrable f 1 μ)
    (htends : ∀ᵐ (x : α) ∂μ, Tendsto (fun n ↦ f n x) u (𝓝 (g x))) :
    Integrable g μ :=
  memLp_one_iff_integrable.mp (hUI.memLp_of_ae_tendsto htends)

end UniformIntegrable

end MeasureTheory
