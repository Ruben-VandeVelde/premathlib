import analysis.complex.basic
import analysis.normed_space.operator_norm
import analysis.normed_space.hahn_banach
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

variables  {F : Type*} [normed_group F] [normed_space ℂ F]

noncomputable def c (f : F →L[ℂ] ℂ) := λ z: F, ((f z).re : ℂ) - (f (I • z)).re * I

-- (1) We merken op dat φ 0 ∈ L(Y, C) volledig bepaald is door Re φ 0 : omdat
--     φ 0 (iy) = iφ 0 (y), is Im φ 0 (y) = − Re φ 0 (iy) voor elke y ∈ Y .
lemma x (f : F →L[ℂ] ℂ) :
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

-- (4) Geı̈nspireerd door de uitdrukking van Im φ 0 stellen we
--     φ(x) := φ r (x) − iφ r (ix) voor elke x ∈ X.

noncomputable def linear_map.extend_to_C
    {F' : Type*} [normed_group F'] [normed_space ℂ F'] (fr : F' →ₗ[ℝ] ℝ)
    : F' →ₗ[ℂ] ℂ := begin
    let fc := λ z, (fr.to_fun (z) : ℂ) - I * fr.to_fun (I • z),
    have add : ∀ (x y : F'), fc (add_group.add x y) = fc x + fc y,
    {
        intros,
        calc
            ((fr.to_fun (x + y)): ℂ ) - I * fr.to_fun (I • (x + y))
            = ((fr.to_fun (x + y)): ℂ ) - I * fr.to_fun (I • x + I • y) : by rw smul_add
        ... = ((fr.to_fun x + fr.to_fun y) : ℂ) - I * fr.to_fun (I • x + I • y) : by rw [ ←complex.of_real_add, fr.add]
        ... = ((fr.to_fun x + fr.to_fun y) : ℂ) - I * (fr.to_fun (I • x) + fr.to_fun (I • y)) : by rw [ ←complex.of_real_add (fr.to_fun (I • x)), fr.add]
        ... = fr.to_fun x - I * fr.to_fun (I • x) + (fr.to_fun y  - I * fr.to_fun (I • y)) : by ring,
    },

exact { to_fun := fc,
  add := add,
  smul := begin
    let fc := λ z, (fr.to_fun (z) : ℂ) - I * fr.to_fun (I • z),
    have ℝ_linear : ∀ (c: ℝ) (x: F'), fc (c • x) = c * fc x,
    {
        intros,
        have hx' : ∀ x': F', fr.to_fun (c • x') = c * fr.to_fun (x'),
        {
            intros,
            rw [fr.smul, smul_eq_mul],
        },

        have : I * fr.to_fun (I • (c • x)) = c * (I * fr.to_fun (I • x)),
        {
            calc
                I * fr.to_fun (I • (c • x))
                = I * fr.to_fun (I • ((c:ℂ) • x)) : by refl
            ... = I * fr.to_fun ((c:ℂ) • (I • x)) : by rw smul_comm I _ x
            ... = I * fr.to_fun (c • (I • x)) : by refl
            ... = I * (c * fr.to_fun (I • x)) : by rw [hx' (I • x), complex.of_real_mul]
            ... = c * (I * fr.to_fun (I • x)) : by ring,
        },

        calc
            (fr.to_fun (c • x) : ℂ) - I * fr.to_fun (I • (c • x))
            = ((c * fr.to_fun x) : ℂ) - I * fr.to_fun (I • (c • x)) : by rw [←complex.of_real_mul, hx']
        ... = ((c * fr.to_fun x) : ℂ) - I * fr.to_fun (I • ((c:ℂ) • x)) : by refl
        ... = ((c * fr.to_fun x) : ℂ) - I * fr.to_fun ((c:ℂ) • (I • x)) : by rw smul_comm I _ x
        ... = ((c * fr.to_fun x) : ℂ) - I * fr.to_fun (c • (I • x)) : by refl
        ... = ((c * fr.to_fun x) : ℂ) - I * (c * fr.to_fun (I • x)) : by rw [←complex.of_real_mul _ (fr.to_fun (I • x)), hx']
        ... = ((c * fr.to_fun x) : ℂ) - (c * (I * fr.to_fun (I • x))) : by ring
        ... = c * (fr.to_fun x - I * fr.to_fun (I • x)) : by ring,
    },
    have hi : ∀ (x: F'), fc (I • x) = I * fc x,
    {
        intros,
        have := fr.smul,
        calc fc (I • x)
            = (fr.to_fun (I • x) : ℂ) - I * fr.to_fun (I • I • x) : rfl
        ... = (fr.to_fun (I • x) : ℂ) - I * fr.to_fun ((I * I) • x) : by rw [mul_smul]
        ... = (fr.to_fun (I • x) : ℂ) - I * fr.to_fun ((-1: ℂ) • x) : by rw [I_mul_I]
        ... = (fr.to_fun (I • x) : ℂ) - I * fr.to_fun (((-1: ℝ) : ℂ) • x) : by rw [of_real_neg, of_real_one]
        ... = (fr.to_fun (I • x) : ℂ) - I * fr.to_fun ((-1 : ℝ) • x) : by refl
        ... = (fr.to_fun (I • x) : ℂ) - I * (((-1 : ℝ ) •  fr.to_fun x: ℝ ) : ℂ ) : by rw fr.smul (-1)
        ... = (fr.to_fun (I • x) : ℂ) - I * (((-1 : ℝ ) *  fr.to_fun x: ℝ ) : ℂ ) : by rw smul_eq_mul
        ... = (fr.to_fun (I • x) : ℂ) - (I * (-1 : ℝ )) *  fr.to_fun x : by rw [of_real_mul, mul_assoc]
        ... = (fr.to_fun (I • x) : ℂ) - (-1 * I) *  fr.to_fun x : by rw [mul_comm I, of_real_neg, of_real_one]
        ... = (fr.to_fun (I • x) : ℂ) - -1 * (I * fr.to_fun x) : by rw [mul_assoc]
        ... = (fr.to_fun (I • x) : ℂ) + (I * fr.to_fun x) : by rw [neg_one_mul, sub_neg_eq_add]
        ... = (I * fr.to_fun x) + fr.to_fun (I • x) : by rw [add_comm]
        ... = (I * fr.to_fun x) - (I * I) * fr.to_fun (I • x) : by rw [I_mul_I, neg_one_mul, sub_neg_eq_add]
        ... = (I * fr.to_fun x) - I * (I * fr.to_fun (I • x)) : by rw [mul_assoc]
        ... = I * fc x : by rw mul_sub,
    },
    intros,
    let a : ℂ := c.re,
    let b : ℂ := c.im,
    have add' : fc (a • x + (b * I) • x) = fc (a • x) + fc ((b * I) • x) := add ((a • x)) (((b * I) • x)),
    calc
        fc (c • x)
        = fc ((a + b * I) • x) : by rw [re_add_im c]
    ... = fc (a • x + (b * I) • x) : by rw add_smul
    ... = fc (a • x) + fc ((b * I) • x) : by rw add'
    ... = fc (c.re • x) + fc ((b * I) • x) : rfl
    ... = a * fc x + fc ((b * I) • x) : by rw ℝ_linear
    ... = a * fc x + fc (b • I • x) : by rw mul_smul
    ... = a * fc x + fc (c.im • I • x) : rfl
    ... = a * fc x + b * fc (I • x) : by rw ℝ_linear
    ... = a * fc x + b * (I * fc x) : by rw hi
    ... = a * fc x + (b * I) * fc x : by rw mul_assoc
    ... = (a + b * I) * fc x : by rw add_mul
    ... = c * fc x : by rw [re_add_im c],
  end
}
end

noncomputable def continuous_linear_map.extend_to_C
    {F' : Type*} [normed_group F'] [normed_space ℂ F'] (fr : F' →L[ℝ] ℝ)
    : F' →L[ℂ] ℂ := begin
    let lm := @linear_map.extend_to_C F' _ _ fr,
    refine (lm.mk_continuous ∥fr∥) _,
    begin
        intros,
        dsimp only [lm],
        classical,
        by_cases lm x = 0,
        {
            rw [h, norm_zero],
            apply mul_nonneg'; exact norm_nonneg _,
        },
        let fx := (lm x)⁻¹,
        let norm := fx / fx.abs,
        have : norm.abs = 1,
        {
            simp only [abs_of_real, of_real_inv, complex.abs_div, complex.abs_inv, complex.abs_abs],
            apply div_self,
            apply inv_ne_zero,
            dsimp [(≠)],
            rw complex.abs_eq_zero,
            exact h,
        },
        have : (norm * lm x).im = 0,
        {
            dsimp only [norm, fx],
            rw div_mul_eq_mul_div,
            rw inv_mul_cancel h,
            rw [←complex.of_real_one, ←of_real_div, of_real_im],
        },
        have : (lm (norm • x)).im = 0,
        {
            unfold_coes at *,
            rw [lm.smul, smul_eq_mul],
            assumption,
        },
        have : lm (norm • x) = fr (norm • x),
        {
            ext,
            {
                unfold_coes at *,
                calc (lm.to_fun (norm • x)).re
                    = ((fr.to_linear_map.to_fun (norm • x) : ℂ) - I * fr.to_linear_map.to_fun (I • (norm • x))).re : rfl
                ... = (fr.to_linear_map.to_fun (norm • x) : ℂ).re - (I * fr.to_linear_map.to_fun (I • (norm • x))).re : by rw sub_re
                ... = (fr.to_linear_map.to_fun (norm • x) : ℂ).re - ((fr.to_linear_map.to_fun (I • (norm • x)): ℂ) * I).re : by rw mul_comm
                ... = (fr.to_linear_map.to_fun (norm • x) : ℂ).re : by rw [smul_re, I_re, mul_zero, sub_zero],
            },
            rw of_real_im,
            unfold_coes at *,
            rw [lm.smul, smul_eq_mul],
            assumption,
        },
        have : ∥lm x∥ = ∥fr (norm • x)∥,
        {
            rw [complex.norm_eq_abs, real.norm_eq_abs, ←abs_of_real],
            calc (lm x).abs
                = norm.abs * (lm x).abs : by rw [‹norm.abs = 1›, one_mul]
            ... = (norm * lm x).abs : by rw complex.abs_mul
            ... = (lm (norm • x)).abs : by {unfold_coes, rw [←smul_eq_mul, lm.smul]}
            ... = ((fr (norm • x)) : ℂ).abs : by rw this
        },
        rw this,

        calc ∥fr (norm • x)∥
            ≤ ∥fr∥ * ∥norm • x∥ : continuous_linear_map.le_op_norm _ _
        ... = ∥fr∥ * (∥norm∥ * ∥x∥) : by rw norm_smul
        ... = ∥fr∥ * ∥x∥ : by rw [norm_eq_abs, ‹norm.abs = 1›, one_mul],
    end,
end

lemma d (p : subspace ℂ   F) (f : p →L[ℂ] ℂ) :
    ∃ g : F →L[ℂ] ℂ, (∀ x : (restrict_scalars p), g x = f x) ∧ ∥g∥ = ∥f∥
    := begin
    have := z p f,
    cases this with g hg,
    use continuous_linear_map.extend_to_C g,
    split,
    {
        intros,
        sorry,
    },
    sorry,
end