import analysis.complex.basic
import analysis.normed_space.operator_norm
import analysis.normed_space.hahn_banach
import .extend
open complex


-- Stelling 2.5.7 (Hahn-Banach, complexe versie).
--
-- Zij X (F) een complexe genormeerde ruimte,
-- Y (p) ≤ X (F) en
-- φ 0 ∈ L(Y (p), C).
-- Dan bestaat een uitbreiding van φ 0 tot φ ∈ L(X (F), C)
-- met ∥φ∥L(X(F),C) = ∥φ 0∥L(Y(p),C) .

variables  {F : Type*} [normed_group F] [normed_space ℂ F]

noncomputable def re_of (f : F →L[ℂ ] ℂ) : F →L[ℝ] ℝ :=
continuous_linear_map.re.comp $ f.restrict_scalars ℝ

lemma re_of_apply (f : F →L[ℂ] ℂ) (x: F) : re_of f x = (f x).re := rfl

noncomputable def c (f : F →L[ℂ] ℂ) := λ z: F, ((f z).re : ℂ) - I * (f (I • z)).re

-- (1) We merken op dat φ 0 ∈ L(Y, C) volledig bepaald is door Re φ 0 : omdat
--     φ 0 (iy) = iφ 0 (y), is Im φ 0 (y) = − Re φ 0 (iy) voor elke y ∈ Y .
lemma xx (f : F →L[ℂ] ℂ) : ∀ z, f z = c f z :=
begin
    intro,
    dsimp [c],
    ext,
    { simp only [sub_re, of_real_re, mul_re, I_re, of_real_im, zero_mul, mul_zero, sub_zero] },

    simp only [
        sub_im, of_real_im, zero_sub, mul_im, I_re,
        zero_mul, zero_add, I_im, one_mul, of_real_re,
        continuous_linear_map.map_smul, smul_eq_mul, mul_re, neg_neg],
end

noncomputable def restrict_scalars
    {G : Type*} [normed_group G] [normed_space ℂ G] (p: subspace ℂ G) :
    subspace ℝ G := p.restrict_scalars ℝ

-- (3) D.m.v. stelling 2.5.4 vinden we een (R-lineaire) uitbreiding φ r ∈ L(X(F), R)
--     van Re φ 0 met ∥φ r∥L(X,R) = ∥Re φ 0∥L(Y(p),R) .
--          f = Re φ 0 = re_of φ 0 : p →L[ℝ] ℝ
--          p = Y ≤_ℂ X = F
--          → φ r = g: F →L[ℝ] ℝ
private lemma apply_real (p : subspace ℂ F) (f' : p →L[ℝ] ℝ) :
    ∃ g : F →L[ℝ] ℝ, (∀ x : restrict_scalars p, g x = f' x) ∧ ∥g∥ = ∥f'∥ :=
    exists_extension_norm_eq (p.restrict_scalars ℝ) f'

theorem complex.exists_extension_norm_eq (p : subspace ℂ F) (f : p →L[ℂ] ℂ) :
    ∃ g : F →L[ℂ] ℂ, (∀ x : p, g x = f x) ∧ ∥g∥ = ∥f∥ :=
begin
    rcases apply_real p (re_of f) with ⟨g, ⟨hextends, hnormeq⟩⟩,
    use g.extend_to_C,
    have : ∀ x : p, (g.extend_to_C) x = f x,
    {
        intros,
        let ix : ↥p := I • x,
        have : g.extend_to_C x = (f x).re - I * (f (I • x)).re,
        calc g.extend_to_C x
            = (g x) - I * (g ix) : rfl
        ... = (g x) - I * re_of f (I • x) : by rw hextends ix
        ... = (g x) - I * (f (I • x)).re : by rw re_of_apply
        ... = ((re_of f) x) - I * (f (I • x)).re : by rw hextends x
        ... = (f x).re - I * (f (I • x)).re : by rw re_of_apply,
        rw this,
        ext,
        { simp only [sub_re, of_real_re, mul_re, I_re, of_real_im, zero_mul, mul_zero, sub_zero] },

        simp only [
            sub_im, of_real_im, zero_sub, mul_im, I_re,
            zero_mul, zero_add, I_im, one_mul, of_real_re,
            continuous_linear_map.map_smul, smul_eq_mul, mul_re, neg_neg],
    },

    split,
    assumption,

    refine le_antisymm _ _,
    {
        calc ∥g.extend_to_C∥
            ≤ ∥g∥ : g.extend_to_C.op_norm_le_bound g.op_norm_nonneg (norm_bound _)
        ... = ∥re_of f∥ : hnormeq
        ... ≤ ∥continuous_linear_map.re∥ * ∥f∥ : continuous_linear_map.op_norm_comp_le _ _
        ... = ∥f∥ : by rw [complex.continuous_linear_map.re_norm, one_mul],
    },

    exact f.op_norm_le_bound g.extend_to_C.op_norm_nonneg (λ x, this x ▸ g.extend_to_C.le_op_norm x),
end