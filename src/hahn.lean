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

lemma a (z: ℂ ) : (I * z).re = -z.im := begin
    rw [mul_re, I_re, I_im],
    ring,
end
lemma a' (z: ℂ ) : (I * z).im = z.re := begin
    rw [mul_im, I_re, I_im],
    ring,
end

lemma b: - I * I = (1: ℂ) := by norm_num

noncomputable def re_of {F' : Type*} [normed_group F'] [normed_space ℂ F'] (f : F' →L[ℂ ] ℂ)
    : F' →L[ℝ] ℝ
    := continuous_linear_map.re.comp $ f.restrict_scalars ℝ

lemma re_of_apply {F' : Type*} [normed_group F'] [normed_space ℂ F'] (f : F' →L[ℂ ] ℂ) (x: F')
    : (re_of f) x = (f x).re
    := begin
    dsimp [re_of],
    refl,
end

variables  {F : Type*} [normed_group F] [normed_space ℂ F]

noncomputable def c (f : F →L[ℂ] ℂ) := λ z: F, ((f z).re : ℂ) - (f (I • z)).re * I

-- (1) We merken op dat φ 0 ∈ L(Y, C) volledig bepaald is door Re φ 0 : omdat
--     φ 0 (iy) = iφ 0 (y), is Im φ 0 (y) = − Re φ 0 (iy) voor elke y ∈ Y .
lemma xx (f : F →L[ℂ] ℂ) :
  ∀ z, f z = c f z := begin
    intro,
    rw c,
    ext,
    rw [sub_re, of_real_re, mul_re, I_re, of_real_im],
    ring,

    rw [sub_im, mul_im, of_real_im, of_real_im, I_im, of_real_re],
    ring,
    calc (f z).im
        = (f ((1: ℂ) • z)).im : by rw one_smul
    ... = (f (((-I) * I) • z)).im : by rw (show - I * I = (1: ℂ), by norm_num)
    ... = (f ((-I) •  I • z)).im : by rw mul_smul
    ... = ((-I) * f (I • z)).im : by rw [continuous_linear_map.map_smul, smul_eq_mul]
    ... = - (f (I • z)).re : by rw [←neg_mul_eq_neg_mul, neg_im, a'],
end

-- (2) Bovendien is Re φ 0 ∈ L(Y, R): Y is een C-vectorruimte, en dus ook een
--     R-vectorruimte.
--     De R-lineariteit van Re φ 0 volgt eenvoudig uit de C-lineariteit van φ 0 .
--          reestrict_scalars
--     Omdat |Re z| ≤ |z|, voor elke z ∈ C, is ∥Re φ 0∥L(Y,R) ≤ ∥φ 0∥L(Y,C) .
lemma y (f : F →L[ℂ] ℂ) : ∥re_of f∥ ≤ ∥f∥ := begin
    have := continuous_linear_map.op_norm_comp_le
        continuous_linear_map.re
        (f.restrict_scalars ℝ),
    rw [complex.continuous_linear_map.re_norm, one_mul] at this,
    exact this,
end

noncomputable def restrict_scalars
    {G : Type*} [normed_group G] [normed_space ℂ G] (X: subspace ℂ G)
    : subspace ℝ G
    :=
{
    carrier := X.carrier,
    zero := X.zero,
    add := X.add,
    smul := λ (c:ℝ) {x: G}, λ hx, begin
        have : c • x ∈ X.carrier,
        { apply X.smul, assumption, },
        have : (algebra_map ℝ ℂ) c • x = c • x,
        {refl},
        change set.mem ((algebra_map ℝ ℂ) c • x) X.carrier,
        
        rw this,
        assumption,
    end

}

-- (3) D.m.v. stelling 2.5.4 vinden we een (R-lineaire) uitbreiding φ r ∈ L(X(F), R)
--     van Re φ 0 met ∥φ r∥L(X,R) = ∥Re φ 0∥L(Y(p),R) .
--          f = Re φ 0 = re_of φ 0 : p →L[ℝ] ℝ
--          p = Y ≤_ℂ X = F
--          → φ r = g: F →L[ℝ] ℝ
lemma z (p : subspace ℂ F) (f : p →L[ℂ] ℂ) : 
  ∃ g : F →L[ℝ] ℝ, (∀ x : (restrict_scalars p), g x = (re_of f) x) ∧ ∥g∥ = ∥re_of f∥ := begin
    exact exists_extension_norm_eq (p.restrict_scalars ℝ) (re_of f),
end

lemma d (p : subspace ℂ   F) (f : p →L[ℂ] ℂ) :
    ∃ g : F →L[ℂ] ℂ, (∀ x : p, g x = f x) ∧ ∥g∥ = ∥f∥
    := begin
    have := z p f,
    cases this with g hg,
    use continuous_linear_map.extend_to_C g,
    have : ∀ (x : p), (g.extend_to_C) x = f x,
    {
        intros,
        have := hg.1 x,
        have ttt := xx f x,
        rw ttt,
        dsimp [c],
        rw ←re_of_apply,
        rw ←this,
        let ix : ↥p := I • x,
        rw ← (show ix = I • x, by refl),
        rw ←re_of_apply,
        rw ←(hg.1 ix),
        rw mul_comm,
        refl,
    },

    split,
    assumption,

    refine le_antisymm _ _,
    have := continuous_linear_map.op_norm_le_bound
        (@continuous_linear_map.extend_to_C _ _ _ (g))
        (continuous_linear_map.op_norm_nonneg (g))
        (norm_bound _),
    calc  ∥g.extend_to_C∥ ≤ ∥g∥ : this
    ... = ∥re_of f∥ : hg.2
    ... ≤ ∥f∥ : y _,

    refine continuous_linear_map.op_norm_le_bound _ _ _,
    exact continuous_linear_map.op_norm_nonneg _,

    intros,
    rw ←this,
    exact  continuous_linear_map.le_op_norm _ _,
end