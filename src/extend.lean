import analysis.complex.basic
import analysis.normed_space.operator_norm
import analysis.normed_space.hahn_banach
open complex

variables  {F : Type*} [normed_group F] [normed_space ℂ F]

noncomputable def linear_map.extend_to_C
    {F' : Type*} [normed_group F'] [normed_space ℂ F'] (fr : F' →ₗ[ℝ] ℝ)
    : F' →ₗ[ℂ] ℂ :=
begin
    let fc := λ z, (fr.to_fun (z) : ℂ) - I * fr.to_fun (I • z),
    have add : ∀ (x y : F'), fc (x + y) = fc x + fc y,
    {
        intros,
        calc
            ((fr.to_fun (x + y)): ℂ ) - I * fr.to_fun (I • (x + y))
            = ((fr.to_fun (x + y)): ℂ ) - I * fr.to_fun (I • x + I • y) : by rw smul_add
        ... = ((fr.to_fun x + fr.to_fun y) : ℂ) - I * fr.to_fun (I • x + I • y) : by rw [ ←complex.of_real_add, fr.add]
        ... = ((fr.to_fun x + fr.to_fun y) : ℂ) - I * (fr.to_fun (I • x) + fr.to_fun (I • y)) : by rw [ ←complex.of_real_add (fr.to_fun (I • x)), fr.add]
        ... = fr.to_fun x - I * fr.to_fun (I • x) + (fr.to_fun y  - I * fr.to_fun (I • y)) : by ring,
    },

    have smul_ℝ : ∀ (c: ℝ) (x: F'), fc (c • x) = c * fc x,
    {
        intros,
        calc
            (fr.to_fun (c • x) : ℂ) - I * fr.to_fun (I • (c • x))
            = ((c * fr.to_fun x) : ℂ) - I * fr.to_fun (I • (c • x)) : by rw [←complex.of_real_mul, fr.smul, smul_eq_mul]
        ... = ((c * fr.to_fun x) : ℂ) - I * fr.to_fun (I • ((c:ℂ) • x)) : by refl
        ... = ((c * fr.to_fun x) : ℂ) - I * fr.to_fun ((c:ℂ) • (I • x)) : by rw smul_comm I _ x
        ... = ((c * fr.to_fun x) : ℂ) - I * fr.to_fun (c • (I • x)) : by refl
        ... = ((c * fr.to_fun x) : ℂ) - I * (c * fr.to_fun (I • x)) : by rw [←complex.of_real_mul _ (fr.to_fun (I • x)), fr.smul, smul_eq_mul]
        ... = ((c * fr.to_fun x) : ℂ) - (c * (I * fr.to_fun (I • x))) : by ring
        ... = c * (fr.to_fun x - I * fr.to_fun (I • x)) : by ring,
    },

    have smul_I : ∀ (x: F'), fc (I • x) = I * fc x,
    {
        intros,
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

    have smul_ℂ : ∀ (c : ℂ) (x : F'), fc (c • x) = c • fc x,
    {
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
        ... = a * fc x + fc ((b * I) • x) : by rw smul_ℝ
        ... = a * fc x + fc (b • I • x) : by rw mul_smul
        ... = a * fc x + fc (c.im • I • x) : rfl
        ... = a * fc x + b * fc (I • x) : by rw smul_ℝ
        ... = a * fc x + b * (I * fc x) : by rw smul_I
        ... = a * fc x + (b * I) * fc x : by rw mul_assoc
        ... = (a + b * I) * fc x : by rw add_mul
        ... = c * fc x : by rw [re_add_im c],
    },

    exact { to_fun := fc, add := add, smul := smul_ℂ }
end

lemma norm_bound
    {F' : Type*} [normed_group F'] [normed_space ℂ F'] (fr : F' →L[ℝ] ℝ)
    : ∀ (x : F'), ∥(@linear_map.extend_to_C F' _ _ fr) x∥ ≤ ∥fr∥ * ∥x∥
:= begin
        intros,
        let lm := @linear_map.extend_to_C F' _ _ fr,
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
end

noncomputable def continuous_linear_map.extend_to_C
    {F' : Type*} [normed_group F'] [normed_space ℂ F'] (fr : F' →L[ℝ] ℝ)
    : F' →L[ℂ] ℂ := begin
    let lm := @linear_map.extend_to_C F' _ _ fr,
    exact (lm.mk_continuous ∥fr∥) (norm_bound _),
end