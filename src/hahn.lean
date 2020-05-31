import analysis.complex.basic
import analysis.normed_space.operator_norm
import analysis.normed_space.hahn_banach
import .extend

open complex

variables {F : Type*} [normed_group F] [normed_space ℂ F]

noncomputable def restrict_scalars (p: subspace ℂ F) : subspace ℝ F := p.restrict_scalars ℝ

private lemma apply_real (p : subspace ℂ F) (f' : p →L[ℝ] ℝ) :
  ∃ g : F →L[ℝ] ℝ, (∀ x : restrict_scalars p, g x = f' x) ∧ ∥g∥ = ∥f'∥ :=
  exists_extension_norm_eq (p.restrict_scalars ℝ) f'

theorem complex.exists_extension_norm_eq (p : subspace ℂ F) (f : p →L[ℂ] ℂ) :
  ∃ g : F →L[ℂ] ℂ, (∀ x : p, g x = f x) ∧ ∥g∥ = ∥f∥ :=
begin
  -- Let `fr: p →L[ℝ] ℝ` be the real part of `f`.
  let fr := continuous_linear_map.re.comp (f.restrict_scalars ℝ),
  have fr_apply : ∀ x, fr x = (f x).re := λ x, rfl,

  -- Use the real version to get a norm-preserving extension of `fr`, which we'll call `g: F →L[ℝ] ℝ`.
  rcases apply_real p fr with ⟨g, ⟨hextends, hnormeq⟩⟩,

  -- Now `g` can be extended to the `F →L[ℂ] ℂ` we need.
  use g.extend_to_C,

  -- It is an extension of `f`.
  have : ∀ x : p, g.extend_to_C x = f x,
  {
    intros,
    change (g x : ℂ) - I * g ((I • x) : p) = f x,
    rw [sub_eq_add_neg, neg_mul_eq_mul_neg, ←of_real_neg, mul_comm, ←mk_eq_add_mul_I],
    ext,
    { rw [hextends, fr_apply] },
    rw [hextends (I • x : p), fr_apply, continuous_linear_map.map_smul,
      algebra.id.smul_eq_mul, mul_re, I_re, zero_mul, zero_sub, neg_neg, I_im, one_mul],
  },

  split,
  assumption,

  -- And we derive the equality of the norms by bounding on both sides.
  refine le_antisymm _ _,
  {
    calc ∥g.extend_to_C∥
        ≤ ∥g∥ : g.extend_to_C.op_norm_le_bound g.op_norm_nonneg (norm_bound _)
    ... = ∥fr∥ : hnormeq
    ... ≤ ∥continuous_linear_map.re∥ * ∥f∥ : continuous_linear_map.op_norm_comp_le _ _
    ... = ∥f∥ : by rw [complex.continuous_linear_map.re_norm, one_mul],
  },

  exact f.op_norm_le_bound g.extend_to_C.op_norm_nonneg (λ x, this x ▸ g.extend_to_C.le_op_norm x),
end