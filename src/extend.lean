import analysis.complex.basic
import analysis.normed_space.operator_norm
import analysis.normed_space.hahn_banach
open complex

variables {F : Type*} [normed_group F] [normed_space ℂ F]

-- Extend `fr : F →ₗ[ℝ] ℝ` to `F →ₗ[ℂ] ℂ` in a way that will also be continuous and have its norm
-- bounded by `∥fr∥` if `fr` is continuous.
noncomputable def linear_map.extend_to_C (fr : F →ₗ[ℝ] ℝ) : F →ₗ[ℂ] ℂ :=
begin
    let fc := λ z, (fr.to_fun (z) : ℂ) - I * fr.to_fun (I • z),
    have add : ∀ x y : F, fc (x + y) = fc x + fc y,
    {
        intros,
        calc
            ((fr.to_fun (x + y)): ℂ ) - I * fr.to_fun (I • (x + y))
            = ((fr.to_fun (x + y)): ℂ ) - I * fr.to_fun (I • x + I • y) : by rw smul_add
        ... = ((fr.to_fun x + fr.to_fun y) : ℂ) - I * fr.to_fun (I • x + I • y) : by rw [←complex.of_real_add, fr.add]
        ... = ((fr.to_fun x + fr.to_fun y) : ℂ) - I * (fr.to_fun (I • x) + fr.to_fun (I • y)) : by rw [←complex.of_real_add (fr.to_fun (I • x)), fr.add]
        ... = fr.to_fun x - I * fr.to_fun (I • x) + (fr.to_fun y  - I * fr.to_fun (I • y)) : by ring,
    },

    have smul_ℝ : ∀ (c : ℝ) (x : F), fc (c • x) = c * fc x,
    {
        intros,
        calc
            (fr.to_fun (c • x) : ℂ) - I * fr.to_fun (I • (c • x))
            = ((c * fr.to_fun x) : ℂ) - I * fr.to_fun (I • (c • x)) : by rw [←complex.of_real_mul, fr.smul, smul_eq_mul]
        ... = ((c * fr.to_fun x) : ℂ) - I * fr.to_fun (I • ((c:ℂ) • x)) : rfl
        ... = ((c * fr.to_fun x) : ℂ) - I * fr.to_fun ((c:ℂ) • (I • x)) : by rw smul_comm I _ x
        ... = ((c * fr.to_fun x) : ℂ) - I * fr.to_fun (c • (I • x)) : rfl
        ... = ((c * fr.to_fun x) : ℂ) - I * (c * fr.to_fun (I • x)) : by rw [←complex.of_real_mul _ (fr.to_fun (I • x)), fr.smul, smul_eq_mul]
        ... = ((c * fr.to_fun x) : ℂ) - (c * (I * fr.to_fun (I • x))) : by ring
        ... = c * (fr.to_fun x - I * fr.to_fun (I • x)) : by ring,
    },

    have smul_I : ∀ x : F, fc (I • x) = I * fc x,
    {
        intros,
        calc fc (I • x)
            = (fr.to_fun (I • x) : ℂ) - I * fr.to_fun (I • I • x) : rfl
        ... = (fr.to_fun (I • x) : ℂ) - I * fr.to_fun (((-1 : ℝ) : ℂ) • x) : by rw [←mul_smul, I_mul_I, of_real_neg, of_real_one]
        ... = (fr.to_fun (I • x) : ℂ) - I * fr.to_fun ((-1 : ℝ) • x) : rfl
        ... = (fr.to_fun (I • x) : ℂ) - I * ((-1 : ℝ) * fr.to_fun x: ℝ) : by rw [fr.smul (-1), smul_eq_mul]
        ... = (fr.to_fun (I • x) : ℂ) - (I * -1) *  fr.to_fun x : by rw [of_real_mul, mul_assoc, of_real_neg, of_real_one]
        ... = (fr.to_fun (I • x) : ℂ) + (I * fr.to_fun x) : by ring
        ... = (I * fr.to_fun x) + fr.to_fun (I • x) : by rw add_comm
        ... = (I * fr.to_fun x) - (I * I) * fr.to_fun (I • x) : by rw [I_mul_I, neg_one_mul, sub_neg_eq_add]
        ... = (I * fr.to_fun x) - I * (I * fr.to_fun (I • x)) : by rw mul_assoc
        ... = I * fc x : by rw mul_sub,
    },

    have smul_ℂ : ∀ (c : ℂ) (x : F), fc (c • x) = c • fc x,
    {
        intros,
        let a : ℂ := c.re,
        let b : ℂ := c.im,
        calc
            fc (c • x)
            = fc ((a + b * I) • x) : by rw re_add_im
        ... = fc (a • x + (b * I) • x) : by rw add_smul
        ... = fc (a • x) + fc ((b * I) • x) : by rw add
        ... = fc (c.re • x) + fc ((b * I) • x) : rfl
        ... = a * fc x + fc ((b * I) • x) : by rw smul_ℝ
        ... = a * fc x + fc (b • I • x) : by rw mul_smul
        ... = a * fc x + fc (c.im • I • x) : rfl
        ... = a * fc x + b * fc (I • x) : by rw smul_ℝ
        ... = a * fc x + b * (I * fc x) : by rw smul_I
        ... = a * fc x + (b * I) * fc x : by rw mul_assoc
        ... = (a + b * I) * fc x : by rw add_mul
        ... = c * fc x : by rw re_add_im c,
    },

    exact { to_fun := fc, add := add, smul := smul_ℂ }
end

-- The norm of the extension is bounded by ∥fr∥.
lemma norm_bound (fr : F →L[ℝ] ℝ) :
    ∀ x : F, ∥fr.to_linear_map.extend_to_C x∥ ≤ ∥fr∥ * ∥x∥ :=
begin
    intros,
    let lm := fr.to_linear_map.extend_to_C,
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
        rw [complex.abs_div, abs_of_real, complex.abs_abs],
        apply div_self,
        dsimp only [fx],
        rw [complex.abs_inv],
        apply inv_ne_zero,
        dsimp only [(≠)],
        rw complex.abs_eq_zero,
        exact h,
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
        calc (lm (norm • x)).im
            = (norm * lm x).im : by { unfold_coes at *, rw [lm.smul, smul_eq_mul], }
        ... = ((lm x)⁻¹ / ((lm x)⁻¹.abs) * lm x).im : rfl
        ... = ((1 / (lm x)⁻¹.abs) : ℂ).im : by rw [div_mul_eq_mul_div, inv_mul_cancel h]
        ... = 0 : by rw [←complex.of_real_one, ←of_real_div, of_real_im],
    },

    calc ∥lm x∥
        = norm.abs * ∥lm x∥ : by rw [‹norm.abs = 1›, one_mul]
    ... = ∥norm * lm x∥ : by rw [normed_field.norm_mul, norm.norm_eq_abs]
    ... = ∥lm (norm • x)∥ : by {unfold_coes, rw [←smul_eq_mul, lm.smul]}
    ... = ∥(fr (norm • x) : ℂ)∥ : by rw this
    ... = ∥fr (norm • x)∥ : by rw norm_real
    ... ≤ ∥fr∥ * ∥norm • x∥ : continuous_linear_map.le_op_norm _ _
    ... = ∥fr∥ * (∥norm∥ * ∥x∥) : by rw norm_smul
    ... = ∥fr∥ * ∥x∥ : by rw [norm_eq_abs, ‹norm.abs = 1›, one_mul],
end

-- Extend `fr : F →L[ℝ] ℝ` to `F →L[ℂ] ℂ`.
noncomputable def continuous_linear_map.extend_to_C (fr : F →L[ℝ] ℝ) : F →L[ℂ] ℂ :=
  fr.to_linear_map.extend_to_C.mk_continuous ∥fr∥ (norm_bound _)
