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

variables  {F : Type*} [normed_group F] [normed_space ℂ F]

noncomputable def re_of (f : F →L[ℂ ] ℂ) : F →L[ℝ] ℝ :=
continuous_linear_map.re.comp $ f.restrict_scalars ℝ

lemma re_of_apply (f : F →L[ℂ] ℂ) (x: F) : re_of f x = (f x).re := rfl

noncomputable def c (f : F →L[ℂ] ℂ) := λ z: F, ((f z).re : ℂ) - (f (I • z)).re * I

-- (1) We merken op dat φ 0 ∈ L(Y, C) volledig bepaald is door Re φ 0 : omdat
--     φ 0 (iy) = iφ 0 (y), is Im φ 0 (y) = − Re φ 0 (iy) voor elke y ∈ Y .
lemma xx (f : F →L[ℂ] ℂ) : ∀ z, f z = c f z :=
begin
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

noncomputable def restrict_scalars
    {G : Type*} [normed_group G] [normed_space ℂ G] (X: subspace ℂ G) :
    subspace ℝ G :=
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
lemma z (p : subspace ℂ F) (f' : p →L[ℝ] ℝ) : 
  ∃ g : F →L[ℝ] ℝ, (∀ x : (restrict_scalars p), g x = f' x) ∧ ∥g∥ = ∥f'∥ := begin
    exact exists_extension_norm_eq (p.restrict_scalars ℝ) f',
end

lemma d (p : subspace ℂ F) (f : p →L[ℂ] ℂ) :
    ∃ g : F →L[ℂ] ℂ, (∀ x : p, g x = f x) ∧ ∥g∥ = ∥f∥
    := begin
    have := z p (re_of f),
    rcases this with ⟨g, ⟨hextends, hnormeq⟩⟩,
    use g.extend_to_C,
    have : ∀ (x : p), (g.extend_to_C) x = f x,
    {
        intros,
        let ix : ↥p := I • x,
        calc g.extend_to_C x
            = (g x) - I * (g ix) : rfl
        ... = (g x) - (g ix) * I : by rw mul_comm
        ... = (g x) - ((re_of f) (I • x)) * I : by rw hextends ix
        ... = (g x) - ((f (I • x)).re) * I : by rw re_of_apply
        ... = ((re_of f) x) - ((f (I • x)).re) * I : by rw hextends x
        ... = ((f x).re) - ((f (I • x)).re) * I : by rw re_of_apply
        ... = c f x : by refl
        ... = f x :  (xx f x).symm,
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