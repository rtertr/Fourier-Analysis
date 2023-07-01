import analysis.calculus.cont_diff_def
import analysis.calculus.mean_value
import analysis.normed_space.finite_dimension
import data.nat.choose.cast
import algebra.geom_sum
import data.complex.basic
import data.nat.choose.sum
import data.complex.exponential
import analysis.normed_space.exponential
import analysis.special_functions.log.basic
import data.polynomial.basic
import data.polynomial.eval
import analysis.schwartz_space
import analysis.normed_space.exponential
import tactic
import topology.basic
import analysis.special_functions.log.base
import analysis.calculus.iterated_deriv
import analysis.special_functions.exp_deriv
import number_theory.dioph
import analysis.complex.real_deriv
import analysis.special_functions.gaussian
import analysis.inner_product_space.calculus
import analysis.calculus.cont_diff
import analysis.fourier.fourier_transform
import order.filter.at_top_bot
import analysis.calculus.parametric_integral

section
open real is_absolute_value finset
open polynomial
open set
open set filter
open schwartz_map
open_locale classical big_operators nat complex_conjugate
open real is_absolute_value finset
open finset
open cau_seq
open complex
open real

noncomputable theory

namespace real

variables {E : Type*}  [normed_add_comm_group E] [normed_space ℂ E] [complete_space E] [measure_theory.measure_space E]
{E' : Type*}  [normed_add_comm_group E'] [inner_product_space ℝ E'] [measure_theory.measure_space E'] [module ℝ E'] [has_measurable_add E']


/- What we proved in our previous document -/
def gaussian_complex  {a : ℂ} (ha :0<a.re) : schwartz_map E' ℂ :=
{ to_fun := λ x : E', complex.exp (-a * ‖x‖^2),
  smooth' := sorry,
  decay' := sorry,}

/- A π-version -/
def gaussian_pi: schwartz_map E' ℂ :=
{ to_fun := λ x : E', complex.exp (-(real.pi: ℂ) * ‖x‖^2),
  smooth' := 
  begin
    refine (gaussian_complex _).smooth',
    norm_cast,
    refine pi_pos,
  end,
  decay' := 
  begin
    refine (gaussian_complex _).decay',
    norm_cast,
    refine pi_pos,
  end,}


theorem integral_gaussian_eq_one (b : ℝ) : 
∫ x, exp (- real.pi * x^2) = 1 :=
begin
  have h :=integral_gaussian real.pi,
  rw [div_self real.pi_ne_zero,sqrt_one] at h,
  exact h,
end

-- # We prove that f' is a schwartz_map

lemma deriv_complex_id {x : ℝ} : 
deriv (λ (y : ℝ), (y : ℂ)) x= 1 := 
has_deriv_at.deriv (has_deriv_at.of_real_comp (has_deriv_at_id x))


lemma deriv_complex_id': deriv (λ (y : ℝ), (y : ℂ))= 1 := 
by {ext1 x, refine has_deriv_at.deriv (has_deriv_at.of_real_comp (has_deriv_at_id x)),}


-- From Mathlib
lemma cont_diff.iterate_deriv :
  ∀ (n : ℕ) {f₂ : ℝ  → ℂ} (hf : cont_diff ℝ ⊤ f₂), cont_diff ℝ  ⊤ (deriv^[n] f₂)
| 0       f₂ hf := hf
| (n + 1) f₂ hf := cont_diff.iterate_deriv n (cont_diff_top_iff_deriv.mp hf).2


lemma cont_diff.deriv_top {f : ℝ → ℂ} (hf : cont_diff ℝ ⊤ f) :  
cont_diff ℝ ⊤ (deriv f) := cont_diff.iterate_deriv 1 hf


def schwartz_deriv (f : schwartz_map ℝ ℂ) : schwartz_map ℝ ℂ :=
{ to_fun := (λ x : ℝ,  deriv f.to_fun x) ,
  smooth' := 
  begin
    refine cont_diff.deriv_top f.smooth',
  end,
  decay' :=
  begin
    have h₁:=f.decay',
    dsimp,
    intro k, intro n,
    specialize h₁ k, specialize h₁ (n+1),
    obtain ⟨C,h₁⟩:=h₁,
    use C, 
    intro x,
    specialize h₁ x,
    rw [iterated_fderiv_eq_equiv_comp, iterated_deriv_eq_iterate, 
    linear_isometry_equiv.norm_map,← iterated_deriv_eq_iterate, 
    ← iterated_deriv_succ'],
    rw [iterated_fderiv_eq_equiv_comp, iterated_deriv_eq_iterate, 
    linear_isometry_equiv.norm_map,← iterated_deriv_eq_iterate] at h₁,
    exact h₁,
  end}


-- # We prove that f^n is a schwartz_map
lemma iterated_deriv_add (f : schwartz_map ℝ ℂ) : 
∀ (n m : ℕ), ∀ x : ℝ,  iterated_deriv n (iterated_deriv m f.to_fun) x = iterated_deriv (n+m) (f.to_fun) x :=
begin 
  intros n m,
  induction m with m hm,
  intro x,
  simp only [iterated_deriv_zero],
  congr,
  rw [iterated_deriv_succ, ← iterated_deriv_succ', iterated_deriv_succ],
  have h₁:= funext hm,
  dsimp at h₁,
  rw h₁,
  rw ← iterated_deriv_succ,
  intro x,
  congr,
end


lemma norm_iterated_fderiv_iterated_deriv {n m : ℕ} (f : schwartz_map ℝ ℂ) {x : ℝ}: 
‖iterated_fderiv ℝ n (iterated_deriv m f.to_fun) x‖ = ‖iterated_fderiv ℝ (n+m) (f.to_fun) x‖ :=
begin 
  have h₁:= iterated_deriv_add f n m x,
  rw [iterated_fderiv_eq_equiv_comp, linear_isometry_equiv.norm_map,iterated_fderiv_eq_equiv_comp, linear_isometry_equiv.norm_map, h₁],
end


def schwartz_iterated_deriv (m : ℕ) (f : schwartz_map ℝ ℂ) : schwartz_map ℝ ℂ :=
{ to_fun := (λ x : ℝ, iterated_deriv m f.to_fun x) ,
  smooth' := by {convert cont_diff.iterate_deriv m f.smooth', rw iterated_deriv_eq_iterate,},
  decay' :=
  begin
    have h₁:=f.decay',
    dsimp only,
    intro k, intro n,
    specialize h₁ k,
    specialize h₁ (n+m),
    obtain ⟨C,h₁⟩:=h₁,
    use C, 
    intro x,
    specialize h₁ x,
    rw norm_iterated_fderiv_iterated_deriv,
    exact h₁,
  end}


-- # We prove that x*f is a schwartz_map
lemma rapid_decay_x_mul_iterated_deriv_zero {k : ℕ} {f : schwartz_map ℝ ℂ}: 
∀ (m : ℕ), ∃ (C : ℝ), ∀ (x : ℝ), ‖x‖ ^ k * ‖iterated_fderiv ℝ 0 (λ (x : ℝ), ↑x * iterated_deriv m f.to_fun x) x‖ ≤ C :=
begin
  have h₁:=f.decay',
  intro m,
  simp only [norm_iterated_fderiv_zero, absolute_value.map_mul, abs_of_real, lattice_ordered_comm_group.abs_abs],
  specialize h₁ (k+1), 
  specialize h₁ m, 
  obtain ⟨C,h₁⟩:=h₁,
  use C,
  intro x,
  specialize h₁ x,
  rw norm_mul,
  have : ‖↑x‖ = ‖x‖, by simp only [norm_eq_abs, complex.norm_eq_abs, abs_of_real, lattice_ordered_comm_group.abs_abs],
  rw [this, ← mul_assoc],
  rw [pow_add,pow_one, iterated_fderiv_eq_equiv_comp,linear_isometry_equiv.norm_map] at h₁,
  exact h₁,
end


lemma cont_diff_deriv_x_mul_iterated_deriv {n m : ℕ} {f : schwartz_map ℝ ℂ}: 
cont_diff ℝ ↑n (deriv (λ (y : ℝ), (y : ℂ)) * iterated_deriv m f.to_fun) :=
begin
  refine cont_diff.mul _ _,
  have hn : ↑n ≤ (⊤ : ℕ∞), by {refine le_of_lt _, exact with_top.coe_lt_top n,},
  refine cont_diff.of_le _ hn,
  refine cont_diff.deriv_top _,
  refine cont_diff.comp _ _,
  exact of_real_clm.cont_diff,
  exact cont_diff_id,
  have h₁:=(schwartz_iterated_deriv _ f).smooth',
  have hn : ↑n ≤ (⊤ : ℕ∞), by {refine le_of_lt _, exact with_top.coe_lt_top n,},
  exact cont_diff.of_le h₁ hn,
end


lemma cont_diff_x_mul_deriv_iterated_deriv {n m : ℕ} {f : schwartz_map ℝ ℂ}: 
cont_diff ℝ ↑n ((λ (y : ℝ), ↑y) * deriv (λ (y : ℝ), iterated_deriv m f.to_fun y)) :=
begin
  refine cont_diff.mul _ _,
  dsimp only,
  exact of_real_clm.cont_diff,
  dsimp only,
  have hn : ↑n ≤ (⊤ : ℕ∞), by {refine le_of_lt _, exact with_top.coe_lt_top n,},
  refine cont_diff.of_le _ hn,
  refine cont_diff.deriv_top _,
  have h₁:=(schwartz_iterated_deriv _ f).smooth',
  exact cont_diff.of_le h₁ (rfl.ge),
end


lemma deriv_mul_rewrite {m : ℕ} {f : schwartz_map ℝ ℂ}: 
deriv (λ (x : ℝ), ↑x * iterated_deriv m f.to_fun x) = deriv (λ (y : ℝ), ↑y) * iterated_deriv m f.to_fun + (λ (y : ℝ), (y : ℂ)) * deriv (λ (y : ℝ), iterated_deriv m f.to_fun y) :=
begin
  ext1,
  rw deriv_mul _ _,  
  simp,
  refine complex.of_real_clm.differentiable_at.comp _ _,
  exact differentiable_at_id,
  {refine differentiable.differentiable_at _, 
  refine cont_diff.differentiable_iterated_deriv m _ (with_top.coe_lt_top m),
  exact f.smooth',},
end 


lemma rapid_decay_x_mul_iterated_deriv {f : schwartz_map ℝ ℂ} :
∀ (k n m : ℕ), ∃ (C : ℝ), ∀ (x : ℝ), ‖x‖ ^ k * ‖iterated_fderiv ℝ n (λ (x : ℝ),(x : ℂ) *((iterated_deriv  m f.to_fun x) : ℂ)) x‖ ≤ C :=
begin
  have h₁:=f.decay',
  intros k n,
  induction n with n hn,
  {exact rapid_decay_x_mul_iterated_deriv_zero,},
  {intro m,
  specialize h₁ k,   specialize h₁ (m+n),
  obtain ⟨C₁,h₁⟩:=h₁, 
  specialize hn (m+1),
  obtain ⟨C₂,hn⟩:=hn,  use (C₁+C₂), 
  intro x,            specialize h₁ x,
  rw [iterated_fderiv_eq_equiv_comp,iterated_deriv_eq_iterate, linear_isometry_equiv.norm_map,← iterated_deriv_eq_iterate,iterated_deriv_succ',
  deriv_mul_rewrite,iterated_deriv_eq_equiv_comp,linear_isometry_equiv.norm_map,iterated_fderiv_add_apply,deriv_complex_id',one_mul],
  have h₂: ‖iterated_fderiv ℝ n ((λ (y : ℝ), (y : ℂ)) * iterated_deriv (m + 1) f.to_fun) x‖ = ‖iterated_fderiv ℝ n (λ (y : ℝ), (y : ℂ)  * iterated_deriv (m + 1) f.to_fun y) x‖, by congr,
  have h₃: ‖x‖^k *‖iterated_fderiv ℝ n (iterated_deriv m f.to_fun) x + iterated_fderiv ℝ n ((λ (y : ℝ), ↑y) * deriv (λ (y : ℝ), iterated_deriv m f.to_fun y)) x‖ ≤ ‖x‖^k * (‖iterated_fderiv ℝ n (iterated_deriv m f.to_fun) x‖ + ‖iterated_fderiv ℝ n ((λ (y : ℝ), ↑y) * deriv (λ (y : ℝ), iterated_deriv m f.to_fun y)) x‖),
    {refine mul_le_mul (rfl.ge) (norm_add_le _ _) _ _,
    apply norm_nonneg _,
    positivity,},
  nth_rewrite 1 ← iterated_deriv_succ at h₃,
  rw [h₂,norm_iterated_fderiv_iterated_deriv, mul_add] at h₃,
  rw add_comm at h₁,
  refine le_trans h₃ (add_le_add h₁ (hn x)),
  exact cont_diff_deriv_x_mul_iterated_deriv,
  exact cont_diff_x_mul_deriv_iterated_deriv,},
end


def schwartz_mul_x  (f : schwartz_map ℝ ℂ) : schwartz_map ℝ ℂ  :=
{ to_fun := λ x : ℝ , (x : ℂ)* f.to_fun x,
  smooth' := 
  begin
    apply cont_diff.mul,
    refine cont_diff.comp _ _,
    exact of_real_clm.cont_diff,
    exact cont_diff_id,
    exact f.smooth',
  end,
  decay' :=
  begin
    have h₁:=rapid_decay_x_mul_iterated_deriv,
    intros k n,
    specialize h₁ k,
    specialize h₁ n,
    specialize h₁ 0,
    rw iterated_deriv_zero at h₁,
    exact h₁,
  end}


-- # We prove that C*f is a schwartz_map
def schwartz_const_mul (C : ℂ) (f : schwartz_map ℝ ℂ) : schwartz_map ℝ ℂ  :=
{ to_fun := λ x : ℝ , (C)* f.to_fun x,
  smooth' := 
  begin
    apply cont_diff.mul cont_diff_const f.smooth',
  end,
  decay' :=
  begin
    have h₁:=f.decay',
    intros k n,
    specialize h₁ k,
    specialize h₁ n,
    obtain ⟨Cf,h₁⟩:=h₁,
    use (‖C‖*Cf),
    intro x,
    specialize h₁ x,
    have h₂: (λ (x : ℝ), C * f.to_fun x) = C • (λ (x : ℝ), f.to_fun x), 
    {ext1,congr,},
    rw [h₂, iterated_fderiv_const_smul_apply  _, norm_smul,← mul_assoc, mul_comm _ (‖C‖), mul_assoc],
    refine mul_le_mul rfl.ge h₁ _ (norm_nonneg _),
    positivity,
    have hn : ↑n ≤ (⊤ : ℕ∞), by {refine le_of_lt _, exact with_top.coe_lt_top n,},
    refine cont_diff.of_le _ hn,
    refine f.smooth',
  end}


-- # We prove that x^j*f is a schwartz_map
lemma rapid_decay_x_mul_pow :
∀ (j : ℕ), ∀ (f : schwartz_map ℝ ℂ), ∀ (k n : ℕ), 
∃ (C : ℝ), ∀ (x : ℝ), ‖x‖ ^ k * ‖iterated_fderiv ℝ n (λ (x : ℝ),(x : ℂ)^j* f.to_fun x) x‖ ≤ C :=
begin
  intros j,
  induction j with j hj,
  intro f,
  simp only [pow_zero, one_mul],
  exact f.decay',
  intro f,
  specialize hj (schwartz_mul_x f),
  have h₂: (schwartz_mul_x f).to_fun = λ x : ℝ , (x : ℂ)* f.to_fun x, by refl,
  rw h₂ at hj,
  dsimp at hj,
  have h₃: (λ (x : ℝ), ↑x ^ j.succ * f.to_fun x) = (λ (x : ℝ), ↑x ^ j * (↑x * f.to_fun x)), 
    ext1,     rw [← mul_assoc, nat.succ_eq_add_one, pow_add, pow_one],
  rw h₃,
  refine hj,
end


def schwartz_mul_x_pow (j : ℕ) (f : schwartz_map ℝ ℂ) : schwartz_map ℝ ℂ  :=
{ to_fun := λ x : ℝ , (x : ℂ)^j * f.to_fun x,
  smooth' := 
  begin
    apply cont_diff.mul,
    refine cont_diff.pow _ j,
    refine cont_diff.comp _ _,
    exact of_real_clm.cont_diff,
    exact cont_diff_id,
    exact f.smooth',
  end,
  decay' :=
  begin
    have h₁:= rapid_decay_x_mul_pow,
    specialize h₁ j,
    specialize h₁ f,
    exact h₁,
  end}


-- # We prove Proposition_1_2_i
lemma integral_smul_const_real  {μ : measure_theory.measure ℝ} (f : ℝ → ℂ) (c : ℂ) :
  ∫ (y : ℝ), f y • c ∂μ = (∫ (y : ℝ), f y ∂μ) • c :=
begin
  refine integral_smul_const _ _,
end


lemma translation_invariance (h : ℝ) (f : ℝ → ℂ) : 
∫ (y : ℝ), f (y-h) = ∫ (y : ℝ),  f y := 
begin
  refine measure_theory.integral_sub_right_eq_self _ _, 
end


lemma proposition_1_2_i (y h : ℝ) (f : schwartz_map ℝ ℂ) : 
real.fourier_integral (λ (y : ℝ), f.to_fun (y+h)) y = cexp (↑(2 * real.pi * y * h) * I) * real.fourier_integral f.to_fun y :=
begin
  rw [real.fourier_integral_eq_integral_exp_smul, real.fourier_integral_eq_integral_exp_smul, mul_comm (cexp (↑(2 * real.pi * y * h) * I))],
  have h₁: (∫ (v : ℝ), cexp (↑((-2) * real.pi * v * y) * I) • f.to_fun v) * cexp (↑(2 * real.pi * y * h) * I) = (∫ (v : ℝ), cexp (↑((-2) * real.pi * v * y) * I) • f.to_fun v) • cexp (↑(2 * real.pi * y * h) * I), by rw smul_eq_mul,
  have h₂: ∫ (v : ℝ), cexp (↑((-2) * real.pi * v * y) * I) • f.to_fun (v +h) = ∫ (v : ℝ), ((λv : ℝ, cexp (↑((-2) * real.pi * (v - h) * y) * I) • f.to_fun v) (v - (-h))),
    {dsimp, congr, ext1, congr, ring_nf, rw neg_neg,},
  rw [h₁,h₂, translation_invariance (-h) ((λ (v : ℝ), cexp (↑((-2) * real.pi * (v - h) * y) * I) • f.to_fun v)),←  integral_smul_const_real _ _],
  dsimp only,
  congr,  ext1,  repeat {rw smul_eq_mul,},
  rw [mul_assoc _ (f.to_fun x) _, mul_comm (f.to_fun x) _, ← mul_assoc _  _ (f.to_fun x)],
  congr,  rw ←complex.exp_add,  congr,
  repeat {rw mul_sub,},  repeat {rw sub_mul,},
  rw ← add_mul _ _ complex.I,  congr,
  have h₃: (-2) * real.pi * h * y = - (2 * real.pi * h * y), by ring_nf,
  rw [h₃, sub_neg_eq_add],
  norm_cast,  ring_nf,
end

-- # we want to prove proposition_1_2_iv. This proof is very long :) see line 932
lemma integration_by_parts (g f : ℝ → ℂ) (N : ℝ) 
(hgdiff : differentiable ℝ g) (hfdiff : differentiable ℝ f) 
(hgcont: continuous (λ (x : ℝ), deriv g x)) (hfcont:continuous (λ (x : ℝ), deriv f x)) : 
∫ (x : ℝ) in -N .. N, (g x * deriv f x) = g (N) * f (N)  - g (-N) * f (-N) -∫ (x : ℝ) in -N .. N, (deriv g x * f x) := 
begin
  apply  interval_integral.integral_mul_deriv_eq_deriv_mul _ _ _ _,
  simp only [set.uIcc_of_le, neg_le_self_iff, nat.cast_nonneg, set.mem_Icc, has_deriv_at_deriv_iff, and_imp],
  intros x hx,
  exact differentiable.differentiable_at hgdiff,
  simp only [set.uIcc_of_le, neg_le_self_iff, nat.cast_nonneg, set.mem_Icc, has_deriv_at_deriv_iff, and_imp],
  intros x hx,
  exact differentiable.differentiable_at hfdiff,
  refine continuous.interval_integrable hgcont (-N) N,
  refine continuous.interval_integrable hfcont (-N) N,
end


lemma schwartz_integration_by_parts (f : schwartz_map ℝ ℂ) {x : ℝ} {N : ℝ}: 
∫ (v : ℝ) in -N..N, (λ v, cexp (↑((-2) * real.pi * v * x) * I)) v * deriv f.to_fun v =  (λ v, cexp (↑((-2) * real.pi * v * x) * I)) N  * f.to_fun N  - (λ v, cexp (↑((-2) * real.pi * v * x) * I)) (-N)  * f.to_fun (-N) -∫ (v : ℝ) in -N .. N, (deriv (λ y, cexp (↑((-2) * real.pi * y * x) * I)) v) * f.to_fun v :=
begin
  rw integration_by_parts (λ v, cexp (↑((-2) * real.pi * v * x) * I)) f.to_fun N _ _ _ _,
  refine differentiable.comp complex.differentiable_exp (differentiable.mul_const _ _),
  refine differentiable.comp of_real_clm.differentiable (differentiable.mul_const _ _),
  refine differentiable.const_mul (differentiable_id) _,
  refine cont_diff.differentiable (f).smooth' _,
  simp only [le_top],
  have h₁: (λ (x_1 : ℝ), deriv (λ (v : ℝ), cexp (↑((-2) * real.pi * v * x) * I)) x_1) = (λ (x_1 : ℝ), (λ (v : ℝ), (cexp (↑((-2) * real.pi * v * x) * I)) * (↑((-2) * real.pi * x) * I)) x_1), 
    ext1,
    rw deriv_cexp _,
    simp only [neg_mul, of_real_neg, of_real_mul, of_real_bit0, of_real_one, deriv.neg', deriv_mul_const_field',   deriv_const_mul_field', neg_inj],
    rw [deriv_complex_id, mul_one],
    refine differentiable.differentiable_at _,
    refine differentiable.mul_const _ _,
    refine differentiable.comp of_real_clm.differentiable (differentiable.mul_const _ _),
    refine differentiable.const_mul (differentiable_id) _,
  rw h₁,
  refine continuous.mul _ _,
  refine continuous.comp complex.continuous_exp _,
  refine continuous.mul _ continuous_const,
  refine continuous.comp of_real_clm.continuous _,
  refine continuous.mul _ continuous_const,
  refine continuous.mul continuous_const continuous_id,
  refine continuous.mul _ continuous_const,
  refine continuous.comp of_real_clm.continuous _,
  refine continuous_const,
  exact cont_diff.continuous (schwartz_deriv f).smooth',
end


lemma rewrite_tendsto (f : schwartz_map ℝ ℂ) {x : ℝ}: 
tendsto (λn : ℝ ,∫ (v : ℝ) in -n..n,cexp (↑((-2) * real.pi * v * x) * I) • deriv f.to_fun v) (filter.at_top) (nhds (∫ (y : ℝ), (cexp (↑((-2) * real.pi * y * x) * I) • f.to_fun y) • (2 * ↑real.pi * I * ↑x))) ↔ tendsto (λn : ℝ ,(cexp (↑((-2) * real.pi * ↑n * x) * I) * f.to_fun ↑n - cexp (↑((-2) * real.pi * -↑n * x) * I) * f.to_fun (-↑n) - ∫ (y : ℝ) in -↑n..↑n, deriv (λ (y : ℝ), cexp (↑((-2) * real.pi * y * x) * I)) y * f.to_fun y)) (filter.at_top) (nhds (∫ (y : ℝ), (0 + 0 + cexp (↑((-2) * real.pi * y * x) * I) • f.to_fun y) • (2 * ↑real.pi * I * ↑x))) :=
begin
  repeat {simp_rw smul_eq_mul},
  split,
  rw metric.tendsto_at_top,
  intros h,
  rw metric.tendsto_at_top, intros ε hε, 
  specialize h ε, specialize h hε, obtain ⟨N,h⟩:=h, 
  use N,
  intros n hn,
  specialize h n, specialize h hn,
  rw schwartz_integration_by_parts f at h,
  simp_rw [zero_add],
  convert h,
  rw metric.tendsto_at_top,
  intros h,
  rw metric.tendsto_at_top, intros ε hε, 
  specialize h ε, specialize h hε, obtain ⟨N,h⟩:=h, 
  use N,
  intros n hn,
  specialize h n, specialize h hn,
  rw schwartz_integration_by_parts f,
  simp_rw [zero_add] at h,
  refine h,
end 


lemma moderate_decrease (f : schwartz_map ℝ ℂ) :
∃ C : ℝ, ∀ x : ℝ, ‖f.to_fun x‖ ≤  (C)/ (1+‖x‖^2) :=
begin
  have h₁:= f.decay',
  have h₂:= f.decay',
  specialize h₁ 0,  specialize h₂ 2,
  specialize h₁ 0,  specialize h₂ 0,
  obtain ⟨C₁,h₁⟩:=h₁,
  obtain ⟨C₂,h₂⟩:=h₂,
  use (C₁ + C₂),
  intro x,
  rw [le_div_iff _, mul_comm, add_mul, one_mul],
  specialize h₁ x,  specialize h₂ x,
  simp only [pow_zero, norm_iterated_fderiv_zero, one_mul] at h₁, simp only [norm_iterated_fderiv_zero] at h₂,
  refine add_le_add h₁ h₂,
  positivity,
end


lemma moderate_decrease_pow (f : schwartz_map ℝ ℂ) :
∀ k : ℕ, ∃ C : ℝ, ∀ x : ℝ, ‖x‖^k * ‖f.to_fun x‖ ≤  (C)/ (1+‖x‖^2) :=
begin
  have h₁:= f.decay',
  have h₂:= f.decay',
  intro k,
  specialize h₁ k,  specialize h₂ (k+2),
  specialize h₁ 0,  specialize h₂ 0,
  obtain ⟨C₁,h₁⟩:=h₁,
  obtain ⟨C₂,h₂⟩:=h₂,
  use (C₁ + C₂),
  intro x,
  rw [le_div_iff _, mul_comm, add_mul, one_mul, ← mul_assoc, ← pow_add _ _, add_comm 2 k],
  specialize h₁ x,  specialize h₂ x,
  simp only [pow_zero, norm_iterated_fderiv_zero, one_mul] at h₁, simp only [norm_iterated_fderiv_zero] at h₂,
  refine add_le_add h₁ h₂,
  positivity,
end


lemma zero_lt_pi_div_two_pos_plus_one: (0: ℝ) <  real.pi/2 + 1:=
begin
  rw ←zero_add (0: ℝ), 
  refine add_lt_add _ zero_lt_one,
  refine real.pi_div_two_pos,
end


lemma zero_le_pi_div_two_pos_plus_one: (0: ℝ) ≤ real.pi/2 + 1:=
begin
  rw ←zero_add (0: ℝ), 
  refine add_le_add _ zero_le_one,
  refine (le_of_lt real.pi_div_two_pos),
end


lemma interval_integrable_schwartz_norm {f : schwartz_map ℝ ℂ} {i: ℕ} {a b : ℝ→ℝ}: 
interval_integrable (λ (x : ℝ), ‖f.to_fun x‖) measure_theory.measure_space.volume (a i) (b i) :=
begin
  refine continuous.interval_integrable _ _ _,
  refine continuous.norm _,
  refine schwartz_map.continuous _,
end


lemma interval_integrable_const_div_one_plus_norm_sq {f : schwartz_map ℝ ℂ} {i: ℕ} {a b : ℝ→ℝ} {C : ℝ}: 
interval_integrable (λ (x : ℝ), (C) / (1 + ‖x‖ ^ 2)) measure_theory.measure_space.volume (a i) (b i) :=
begin
  refine continuous.interval_integrable _ _ _,
  refine continuous.div _ _ _,
  refine continuous_const,
  refine continuous.add (continuous_const) _,
  simp only [norm_eq_abs, pow_bit0_abs],
  refine continuous_pow _,
  intro x, positivity,
end


lemma nonneg_expression1 (f : schwartz_map ℝ ℂ) : 
∀ x : ℝ,  0 ≤ ‖f.to_fun x‖ * (1 + ‖x‖ ^ 2) := by {intro x,positivity,}


lemma nonneg_expression2: ∀ x : ℝ,  0 <  (1 + ‖x‖ ^ 2) := by {intro x, positivity,}


lemma integral_schwartz_le_integral_moderate_decrease 
{f : schwartz_map ℝ ℂ} {i C : ℝ} (h :∀ (x : ℝ), ‖f.to_fun x‖ ≤ C / (1 + ‖x‖ ^ 2)) : 
∫ (x : ℝ) in ((λ y : ℝ ,-‖y‖) i)  ..((λ y : ℝ ,‖y‖) i), ‖f.to_fun x‖ ≤ ∫ (x : ℝ) in ((λ y : ℝ ,-‖y‖) i)..((λ y : ℝ ,‖y‖) i), (C)/ (1+‖x‖^2) :=
begin
  refine interval_integral.integral_mono _ _ _ _, 
  have h₁: (λ y : ℝ,-‖y‖) i ≤ (λ y : ℝ,‖y‖) i, by {simp only [neg_le_self_iff],exact norm_nonneg _,},
  refine h₁,
  {refine continuous.interval_integrable (continuous.norm _) _ _,  refine schwartz_map.continuous f,}, 
  {refine continuous.interval_integrable _ _ _,
  refine continuous.div continuous_const (continuous.add (continuous_const) _) _,
  simp only [norm_eq_abs, pow_bit0_abs],
  refine continuous_pow _,  intro x, positivity,}, 
  exact h,
end


lemma integral_schwartz_norm_bounded {f : schwartz_map ℝ ℂ} (l:filter ℝ) :
∃ I: ℝ,  ∀ᶠ (i : ℝ) in l, ∫ (x : ℝ) in (λ y : ℝ ,-‖y‖) i..(λ y : ℝ ,‖y‖) i, ‖f.to_fun x‖ ≤ I:=
begin
  set a := (λ y : ℝ ,-‖y‖) with ha,
  set b := (λ y : ℝ ,‖y‖) with hb,
  have h₁:=moderate_decrease f,
  obtain ⟨C,h₁⟩:=h₁,
  use ((real.pi/2+1)*((C + C))),
  refine filter.eventually_of_forall _,
  intro i,
  convert le_trans (integral_schwartz_le_integral_moderate_decrease h₁) _,
  have h₄: ∫ (x : ℝ) in a i..b i, (C) / (1 + ‖x‖ ^ 2) = (∫ (x : ℝ) in a i..b i, (1 + x ^ 2)⁻¹) * (C),
    {rw [←smul_eq_mul,←  interval_integral.integral_smul_const], congr, ext1,
    rw [div_eq_mul_one_div, mul_comm, ← smul_eq_mul,inv_eq_one_div],
    simp only [norm_eq_abs, pow_bit0_abs],},
  have hC :0≤ C, by {specialize h₁ i, rw le_div_iff at h₁,  refine le_trans _ h₁,  exact nonneg_expression1 f i,  exact nonneg_expression2 i,},
  rw [h₄, integral_inv_one_add_sq, sub_eq_add_neg, add_mul,mul_add],
  refine add_le_add (mul_le_mul _ rfl.ge hC (le_of_lt zero_lt_pi_div_two_pos_plus_one)) _,
  refine le_trans (le_of_lt (arctan_lt_pi_div_two (b i))) _,
  simp only [le_add_iff_nonneg_right, zero_le_one],
  refine mul_le_mul _ rfl.ge hC (le_of_lt zero_lt_pi_div_two_pos_plus_one),
  {rw neg_le,  refine le_trans _ (le_of_lt (real.neg_pi_div_two_lt_arctan (a i))),
  refine neg_le_neg _,  simp only [le_add_iff_nonneg_right, zero_le_one],},
end


lemma integrable_schwartz_map (f : schwartz_map ℝ ℂ) : 
measure_theory.integrable (λ (v : ℝ), f.to_fun v) measure_theory.measure_space.volume:=
begin  
  have h₁:= integral_schwartz_norm_bounded at_top,
  obtain ⟨I,h₁⟩:=h₁, 
  refine measure_theory.integrable_of_interval_integral_norm_bounded I _ _ _ h₁,
  {intro i,
  refine continuous.integrable_on_Ioc _,
  refine schwartz_map.continuous f,},
  {simp only [tendsto_neg_at_bot_iff], exact tendsto_norm_at_top_at_top,},
  {exact tendsto_norm_at_top_at_top,},
end


lemma integrable_mul_schwartz_map (f : schwartz_map ℝ ℂ) (g : ℝ → ℂ)
(hf : measure_theory.integrable (λ (v : ℝ), f.to_fun v) measure_theory.measure_space.volume)
(hg : ∃(C : ℝ), ∀ x : ℝ, ‖g x‖ ≤ C) (hc : continuous g) :
measure_theory.integrable (λ (v : ℝ), g v * f.to_fun v) measure_theory.measure_space.volume:=
by  refine measure_theory.integrable.bdd_mul hf (continuous.ae_strongly_measurable hc) hg


lemma n_top_integral (f : ℝ→ ℂ) 
(hf : measure_theory.integrable (λ (v : ℝ), f v) measure_theory.measure_space.volume) :
tendsto (λ (n : ℝ), ∫ (v : ℝ) in -n..n, f v) at_top (nhds (∫ (v : ℝ), f v)) :=
begin
  refine measure_theory.interval_integral_tendsto_integral hf _ rfl.ge,
  {simp only [tendsto_neg_at_bot_iff], exact rfl.ge,},
end


lemma n_top_integral_schwartz (f : schwartz_map ℝ ℂ) :
tendsto (λ (n : ℝ), ∫ (v : ℝ) in -n..n, f.to_fun v) at_top (nhds (∫ (v : ℝ), f.to_fun v)) :=
begin
  refine measure_theory.interval_integral_tendsto_integral (integrable_schwartz_map f) _ rfl.ge,
  {simp only [tendsto_neg_at_bot_iff], exact rfl.ge,},
end


lemma deriv_exp_neg_complex_mul  (a : ℂ) :  
∀ (x : ℝ), deriv (λ (x : ℝ), complex.exp (a*x)) x = (λ (x : ℝ), (a) * complex.exp (a*x)) x :=
begin
  intro x,
  rw [deriv.comp, complex.deriv_exp,deriv_mul,deriv_const],
  simp only [neg_mul, zero_mul, zero_add, mul_neg, neg_inj],
  have h₁: deriv (λ (y : ℝ), ↑y) x = (1: ℂ),
    {apply has_deriv_at.deriv _, refine has_deriv_at.of_real_comp _,
    have h₂: deriv  (λ (y : ℝ), y) x = (1),by simp only [differentiable_at_id', nat.cast_bit0, algebra_map.coe_one, pow_one, deriv_id'', mul_one],
    rw ←  h₂,  refine differentiable_at.has_deriv_at _, apply differentiable_at_id',},
  rw h₁,  ring_nf,  apply differentiable_at_const,
  {refine differentiable.differentiable_at _,  refine differentiable.comp of_real_clm.differentiable differentiable_id,},
  {apply differentiable_at.comp,{ apply differentiable_at.cexp,apply differentiable_at_id',},{apply differentiable_at_id',},},
  {norm_cast,  apply differentiable_at.mul,  apply differentiable_at_const, refine differentiable.differentiable_at _,  refine differentiable.comp of_real_clm.differentiable differentiable_id,},
end


lemma norm_deriv_rw {h x : ℝ}: 
‖deriv (λ (y : ℝ), cexp (-(2 * ↑real.pi * ↑y * ↑h * I))) x‖ = ‖deriv (λ (y : ℝ), cexp ((↑((-2) * real.pi * h) * I)* y)) x‖:=
begin 
  congr,ext1 y,repeat {rw ← neg_mul,}, rw [mul_comm _ I, mul_comm _ I], repeat {rw ← mul_assoc,},repeat {rw mul_assoc,},
  rw mul_comm (y : ℂ) _,  rw ← mul_assoc _ (h : ℂ) _, norm_cast, repeat {rw ← mul_assoc,},repeat {rw mul_assoc,},
end


lemma deriv_cexp_bound {h : ℝ} : 
∃ (C : ℝ), ∀ (x : ℝ), ‖deriv (λ (y : ℝ), cexp (↑((-2) * real.pi * y * h) * I)) x‖ ≤ C :=
begin
  use (2 * |real.pi| * |h|),
  intro x,
  simp only [neg_mul, of_real_neg, of_real_mul, of_real_bit0, of_real_one],
  rw [norm_deriv_rw, deriv_exp_neg_complex_mul (↑((-2) * real.pi * h) * I) x],
  simp only [neg_mul, of_real_neg, of_real_mul, of_real_bit0, of_real_one, complex.norm_eq_abs, absolute_value.map_neg,
  absolute_value.map_mul, complex.abs_two, abs_of_real, abs_I, mul_one],
  have h₂: ‖cexp (-(2 * ↑real.pi * ↑h * I * ↑x))‖ = ‖cexp ((↑(-2 * real.pi *h * x))* I)‖,
  {congr,repeat {rw ← neg_mul,}, rw [mul_comm _ I, mul_comm _ I], repeat {rw mul_assoc,}, congr, norm_cast,},
  rw [← complex.norm_eq_abs,h₂, complex.norm_exp_of_real_mul_I _, mul_one],
end


lemma deriv_rw {h : ℝ}: 
deriv (λ (y : ℝ), cexp (-(2 * ↑real.pi * ↑y * ↑h * I))) = deriv (λ (y : ℝ), cexp ((↑((-2) * real.pi * h) * I)* y)) :=
begin 
  congr,ext1 y,repeat {rw ← neg_mul,}, rw [mul_comm _ I, mul_comm _ I], repeat {rw ← mul_assoc,},repeat {rw mul_assoc,},
  rw mul_comm (y : ℂ) _,  rw ← mul_assoc _ (h : ℂ) _, norm_cast, repeat {rw ← mul_assoc,},repeat {rw mul_assoc,},
end


lemma deriv_continous {h : ℝ}: 
continuous (λ (v : ℝ), deriv (λ (y : ℝ), cexp (↑((-2) * real.pi * y * h) * I)) v) :=
begin
  simp only [neg_mul, of_real_neg, of_real_mul, of_real_bit0, of_real_one],
  rw [deriv_rw], 
  have h₁:= deriv_exp_neg_complex_mul (↑((-2) * real.pi * h) * I),
  have h₂:= funext h₁, dsimp only at h₂,
  rw h₂,
  refine continuous.mul continuous_const _,
  refine continuous.cexp (continuous.mul continuous_const _),
  refine continuous.comp of_real_clm.continuous continuous_id,
end


lemma part3_limit  (f : schwartz_map ℝ ℂ) (x : ℝ) :  
tendsto (λ (n : ℝ),∫ (y : ℝ) in -↑n..↑n, deriv (λ (y : ℝ), cexp (↑((-2) * real.pi * y * x) * I)) y * f.to_fun y) at_top (nhds (∫ (y : ℝ), (cexp (↑((-2) * real.pi * y * x) * I) • f.to_fun y) • (-2 * ↑real.pi * I * ↑x))) :=
begin
  have h₁:= n_top_integral (λ (y : ℝ), deriv (λ (y : ℝ),cexp (↑((-2) * real.pi * y * x) * I)) y * f.to_fun y) _,
  convert h₁,  ext1,   repeat {simp_rw smul_eq_mul},
  rw [mul_comm _ (f.to_fun x_1), mul_comm _ (f.to_fun x_1), mul_assoc (f.to_fun x_1) _ _],
  congr,  rw deriv_cexp _,  congr,
  simp only [of_real_neg, of_real_mul, of_real_bit0, of_real_one, deriv.neg', deriv_mul_const_field',  deriv_const_mul_field'],
  rw deriv_complex_id,  ring_nf,
  refine differentiable.differentiable_at _,
  refine differentiable.mul_const _ _,
  refine differentiable.comp of_real_clm.differentiable (differentiable.mul_const _ _),
  refine differentiable.const_mul (differentiable_id) _,
  refine integrable_mul_schwartz_map _ _ (integrable_schwartz_map _) deriv_cexp_bound deriv_continous,
end


lemma N1_le_n {n N N₁ N₂ N₃: ℝ} (h : N= max N₁ (max N₂ N₃)) (hn : n ≥ N) : n ≥ N₁:=
begin
  rw [h, ge_iff_le] at hn,
  rw ge_iff_le,
  apply le_trans _ hn,
  rw le_max_iff,
  left, exact rfl.ge,
end


lemma N2_le_n {n N N₁ N₂ N₃: ℝ} (h : N= max N₁ (max N₂ N₃)) (hn : n ≥ N) : n ≥ N₂:=
begin
  rw [h, ge_iff_le] at hn,
  rw ge_iff_le,
  refine le_trans _ hn,
  rw le_max_iff,
  right, rw le_max_iff,
  left, exact rfl.ge,
end


lemma N3_le_n {n N N₁ N₂ N₃: ℝ} (h : N= max N₁ (max N₂ N₃)) (hn : n ≥ N) : n ≥ N₃:=
begin
  rw h at hn,
  rw ge_iff_le at hn,
  rw ge_iff_le,
  refine le_trans _ hn,
  rw le_max_iff,
  right, rw le_max_iff,
  right, exact rfl.ge,
end


lemma tendsto_const_div_at_top_nhds_0 (C : ℝ) : 
tendsto (λ n : ℝ  , C / n) at_top (nhds 0) :=
begin
  cases le_or_lt  (|C|) 0,
  {rw[← norm_eq_abs, norm_le_zero_iff] at h,  rw h, simp only [zero_div, tendsto_const_nhds_iff],},
  rw metric.tendsto_at_top,
  intros ε hε, 
  use (|C|/ε +1),
  intros n hn, 
  have h₁:=  real.le_norm_self n,
  rw dist_eq_norm,
  simp only [tsub_zero, norm_eq_abs],
  rw ge_iff_le at hn,
  rw [abs_div, div_lt_iff _, mul_comm, ←div_lt_iff _], 
  rw ← le_sub_iff_add_le at hn,
  refine lt_of_le_of_lt hn _,
  rw norm_eq_abs at h₁,
  refine lt_of_lt_of_le _ h₁,
  simp only [sub_lt_self_iff, zero_lt_one],
  exact hε,
  refine lt_of_lt_of_le (lt_of_lt_of_le _ hn) h₁,
  have h₂: |C| / ε < |C| / ε + 1, simp only [lt_add_iff_pos_right, zero_lt_one],
  refine lt_trans _ h₂,
  rw div_eq_mul_inv,
  refine right.mul_pos h _,
  rw inv_pos,
  exact hε,
end


lemma limit_N_pos  (f : schwartz_map ℝ ℂ) {x : ℝ} : 
tendsto (λ (n : ℝ), cexp (↑((-2) * real.pi * ↑n * x) * I) * f.to_fun n) at_top (nhds (0)) :=
begin
  have h₂:=f.decay', 
  specialize h₂ 1,
  specialize h₂ 0,
  obtain ⟨C,h₂⟩:=h₂,
  have h :=tendsto_const_div_at_top_nhds_0, 
  specialize h C,
  rw metric.tendsto_at_top at h,
  rw metric.tendsto_at_top,
  intros ε hε, 
  specialize h ε, specialize h hε, obtain ⟨N,h⟩:=h, 
  use (‖N‖+1),
  intros n hn,
  specialize h n, specialize h _,
  rw ge_iff_le at hn,
  rw ge_iff_le,
  refine le_trans _ hn,
  nth_rewrite 0 ← add_zero N,
  refine add_le_add (real.le_norm_self _) zero_le_one,
  rw [dist_eq_norm,sub_zero, norm_mul, complex.norm_exp_of_real_mul_I, one_mul],
  specialize h₂ n,
  have h₂: ‖n‖ ^ 1 * ‖iterated_fderiv ℝ 0 f.to_fun n‖ ≤ ‖C‖, by refine le_trans h₂ (real.le_norm_self _),
  simp only [pow_one, norm_iterated_fderiv_zero] at h₂,  
  rw [dist_eq_norm, sub_zero,norm_div] at h,
  rw [mul_comm (‖n‖) _ ,← le_div_iff _] at h₂,
  refine lt_of_le_of_lt h₂ _,
  refine h,
  rw ge_iff_le at hn,
  have h₃: ‖N ‖+ 1 ≤ ‖n‖, by refine le_trans hn (real.le_norm_self _),
  refine lt_of_lt_of_le _ h₃,
  positivity,
end


lemma limit_N_neg  (f : schwartz_map ℝ ℂ) {x : ℝ} : 
tendsto (λ (n : ℝ),cexp (↑((-2) * real.pi * -↑n * x) * I) * f.to_fun (-n)) at_top (nhds (0)) :=
begin
  have h₂:=f.decay', 
  specialize h₂ 1,
  specialize h₂ 0,
  obtain ⟨C,h₂⟩:=h₂,
  have h :=tendsto_const_div_at_top_nhds_0, 
  specialize h C,
  rw metric.tendsto_at_top at h,
  rw metric.tendsto_at_top,
  intros ε hε, 
  specialize h ε, specialize h hε, obtain ⟨N,h⟩:=h, 
  use (‖N‖+1),
  intros n hn,
  specialize h n, specialize h _,
  rw ge_iff_le at hn,
  rw ge_iff_le,
  refine le_trans _ hn,
  nth_rewrite 0 ← add_zero N,
  refine add_le_add (real.le_norm_self _) zero_le_one,
  rw dist_eq_norm, rw dist_eq_norm at h,
  rw [sub_zero, norm_mul, complex.norm_exp_of_real_mul_I, one_mul],
  specialize h₂ (-n),
  rw norm_neg at h₂,
  have h₂: ‖n‖ ^ 1 * ‖iterated_fderiv ℝ 0 f.to_fun (-n)‖ ≤ ‖C‖, by refine le_trans h₂ (real.le_norm_self _),
  simp only [pow_one, norm_iterated_fderiv_zero] at h₂,  
  rw sub_zero at h,
  rw [mul_comm (‖n‖) _,← le_div_iff _] at h₂,
  refine lt_of_le_of_lt h₂ _,
  rw norm_div at h,
  refine h,
  rw ge_iff_le at hn,
  have h₃: ‖N ‖+ 1 ≤ ‖n‖, by refine le_trans hn (real.le_norm_self _),
  refine lt_of_lt_of_le _ h₃,
  positivity,
end


lemma hypothesis3 {f : schwartz_map ℝ ℂ} {x : ℝ}: 
tendsto (λn : ℝ ,∫ (v : ℝ) in -n..n,cexp (↑((-2) * real.pi * v * x) * I) • (deriv f.to_fun v)) (filter.at_top) (nhds (∫ (y : ℝ), (cexp (↑((-2) * real.pi * y * x) * I) • f.to_fun y) • (2 * ↑real.pi * I * ↑x))) :=
begin
  rw [rewrite_tendsto f, metric.tendsto_at_top],
  intros ε hε,  
  have h₁: tendsto (λ (n : ℝ), cexp (↑((-2) * real.pi * ↑n * x) * I) * f.to_fun ↑n) at_top (nhds (0)), by refine limit_N_pos f,
  have h₂: tendsto (λ (n : ℝ),cexp (↑((-2) * real.pi * -↑n * x) * I) * f.to_fun (-↑n)) at_top (nhds (0)), by refine limit_N_neg f,
  have h₃:=part3_limit f x,
  rw metric.tendsto_at_top at h₁, rw metric.tendsto_at_top at h₂, rw metric.tendsto_at_top at h₃,
  specialize h₁ (ε/3), specialize h₂ (ε/3), specialize h₃ (ε/3), 
  have h₄: ε/3>0, by positivity,
  specialize h₁ h₄, specialize h₂ h₄, specialize h₃ h₄, 
  repeat {simp_rw sub_eq_add_neg,},
  repeat {simp_rw smul_eq_mul},
  obtain ⟨N₁,h₁⟩:=h₁, obtain ⟨N₂,h₂⟩:=h₂, obtain ⟨N₃,h₃⟩:=h₃,
  set N := max N₁ (max N₂ N₃) with hmax,
  use N,
  intros n hn,
  specialize h₁ n, specialize h₂ n, specialize h₃ n,
  specialize h₁ _, refine N1_le_n hmax hn, specialize h₂ _, exact N2_le_n hmax hn, specialize h₃ _, exact N3_le_n hmax hn,
  rw dist_eq_norm, rw dist_eq_norm at h₁, rw dist_eq_norm at h₂, rw dist_eq_norm at h₃,
  repeat {rw add_assoc,},
  repeat {rw add_sub_assoc,},
  have h₅: ε = ε/3 + (ε/3 + ε/3), by ring_nf,
  rw h₅,
  refine lt_of_le_of_lt ((norm_add_le _ _)) _,
  refine add_lt_add _ _,
  rw sub_zero at h₁, 
  refine h₁,
  refine lt_of_le_of_lt ((norm_add_le _ _)) _,
  refine add_lt_add _ _,
  rw norm_neg,
  rw sub_zero at h₂,
  refine h₂,
  rw ← norm_neg  at h₃,
  convert h₃,
  rw zero_add,
  ring_exp,
  congr,
  rw ← measure_theory.integral_neg,
  congr,
  ext1,
  rw zero_add,
  have h₁: ((-2) * ↑real.pi * I * ↑x) = -(2 * ↑real.pi * I * ↑x), by ring_nf,
  rw [h₁, smul_eq_mul, smul_eq_mul, mul_neg],
end


lemma cexp_bound (h : ℝ) : 
∃ (C : ℝ), ∀ (x : ℝ), ‖cexp (↑((-2) * real.pi * x * h) * I)‖ ≤ C :=
begin
  use 1,
  intro x,
  simp only [neg_mul, of_real_neg, of_real_mul, of_real_bit0, of_real_one],
  have h₂: ‖cexp (-(2 * ↑real.pi * ↑x * ↑h * I))‖ = ‖cexp ((↑(-2 * real.pi *h * x))* I)‖,
  {congr,repeat {rw ← neg_mul,}, rw [mul_comm _ I, mul_comm _ I], repeat {rw mul_assoc,}, congr, norm_cast,rw mul_comm h _,},
  rw [h₂, complex.norm_exp_of_real_mul_I _],
end


lemma integrable_exp_mul_deriv_schwartz {x : ℝ} {f : schwartz_map ℝ ℂ}:
measure_theory.integrable (λ (v : ℝ), cexp (↑((-2) * real.pi * v * x) * I) • deriv f.to_fun v) measure_theory.measure_space.volume:=
begin
  simp_rw smul_eq_mul,
  refine integrable_mul_schwartz_map _ _ (integrable_schwartz_map (schwartz_deriv f)) (cexp_bound _) _,
  refine continuous.cexp _,
  refine continuous.mul _ continuous_const,
  refine continuous.comp of_real_clm.continuous _,
  refine continuous.mul _ continuous_const,
  refine continuous.mul continuous_const continuous_id,
end


lemma proposition_1_2_iv (f : schwartz_map ℝ ℂ) : 
∀ (x : ℝ),real.fourier_integral (deriv f.to_fun) (x)  = 2*real.pi*I*x * real.fourier_integral f.to_fun (x) := 
begin
  intro x,
  have h₁: (∫ (v : ℝ), cexp (↑((-2) * real.pi * v * x) * I) • f.to_fun v) * (2 * ↑real.pi * I * ↑x) = (∫ (v : ℝ), cexp (↑((-2) * real.pi * v * x) * I) • f.to_fun v) • (2 * ↑real.pi * I * ↑x), by rw ← smul_eq_mul,
  rw [real.fourier_integral_eq_integral_exp_smul,real.fourier_integral_eq_integral_exp_smul, mul_comm (2 * ↑real.pi * I * ↑x) _, h₁, ← integral_smul_const_real],
  have h₂: tendsto (λn : ℝ ,∫ (v : ℝ) in -n..n,cexp (↑((-2) * real.pi * v * x) * I) • deriv f.to_fun v) (filter.at_top) (nhds (∫ (v : ℝ), cexp (↑((-2) * real.pi * v * x) * I) • deriv f.to_fun v)), 
    refine n_top_integral _ integrable_exp_mul_deriv_schwartz,
  refine tendsto_nhds_unique_of_frequently_eq (h₂) hypothesis3 _,
  exact frequently_of_forall (congr_fun rfl),
end


-- # We prove proposition_1_2_iv for f^n
lemma proposition_1_2_iv_iterated (n : ℕ) (f : schwartz_map ℝ ℂ) : 
∀ (x : ℝ), real.fourier_integral (iterated_deriv n f.to_fun) (x) = (2*real.pi*I*x)^n * real.fourier_integral f.to_fun (x) :=
begin
  induction n with n hn,
  intro x,
  simp only [iterated_deriv_zero, pow_zero, one_mul],
  rw iterated_deriv_succ,
  have h₁:=proposition_1_2_iv (schwartz_iterated_deriv n f),
  have h₂: (schwartz_iterated_deriv n f).to_fun = (λ x : ℝ, iterated_deriv n f.to_fun x), by refl,  rw h₂ at h₁,
  have h₃:= funext h₁, dsimp at h₃, rw h₃,
  have h₄:= funext hn, dsimp at h₄, rw h₄,
  intro x,
  dsimp,
  rw [nat.succ_eq_add_one, pow_add, mul_comm ((2 * ↑real.pi * I * ↑x) ^ n) ((2 * ↑real.pi * I * ↑x) ^ 1), pow_one, ← mul_assoc],
end


lemma fourier_integral_mul_x_pow {x : ℝ} {n : ℕ} {f : schwartz_map ℝ ℂ} : 
fourier_integral f.to_fun x * ↑x ^ n * (2 * I * ↑real.pi) ^ n * (2 * I * ↑real.pi)⁻¹ ^ n = fourier_integral f.to_fun x * ↑x ^ n :=
begin
  rw [inv_eq_one_div, mul_assoc (fourier_integral f.to_fun x * ↑x ^ n), ← mul_pow, ← div_eq_mul_one_div, div_self _, one_pow, mul_one],
  refine mul_ne_zero (mul_ne_zero (two_ne_zero) (complex.I_ne_zero)) _,
  norm_cast,
  exact real.pi_ne_zero,
end


-- # A rewrite of above statement
lemma proposition_1_2_iv_iterated_lemma (n : ℕ) (f : schwartz_map ℝ ℂ) : 
∀ (x : ℝ), (1/(2*(real.pi: ℂ)*I))^n*real.fourier_integral (iterated_deriv n f.to_fun) (x) = (x)^n * real.fourier_integral f.to_fun (x) :=
begin
  have h₁:= proposition_1_2_iv_iterated n f,
  intro x,
  specialize h₁ x,
  have h₂: (2 * ↑real.pi * I * ↑x) ^ n = (2 * ↑real.pi * I)^n * (↑x) ^ n, by ring_exp,
  have h₃: (1/(2 * ↑real.pi * I))^n ≠ 0, 
    {refine pow_ne_zero _ _, 
    rw one_div,
    refine inv_ne_zero (mul_ne_zero (mul_ne_zero (two_ne_zero) _) (complex.I_ne_zero)),
    norm_cast,
    exact real.pi_ne_zero,},
  have h₄: (1 / (2 * ↑real.pi * I)) ^ n * ((2 * ↑real.pi * I) ^ n * ↑x ^ n * fourier_integral f.to_fun x) =   ↑x ^ n * fourier_integral f.to_fun x, by {ring_nf, exact fourier_integral_mul_x_pow,},
  rw [h₂,← mul_right_inj' h₃] at h₁,
  rw [h₁, h₄],
end


def gaussian_complex_pi: schwartz_map ℝ ℂ :=
{ to_fun := λ x : ℝ, complex.exp (-real.pi * x ^ 2),
  smooth' := 
  begin
    sorry,
  end,
  decay' :=
  begin
    sorry,
  end}


lemma gaussian_complex_to_fun : gaussian_complex_pi.to_fun =λ x : ℝ, complex.exp (-real.pi * x ^ 2) := by refl


lemma fourier_transform_eq_gaussian2 : 
∀ x : ℝ, real.fourier_integral gaussian_complex_pi.to_fun x =gaussian_complex_pi.to_fun x :=
begin
  intro x,
  rw  gaussian_complex_to_fun,
  have h₀: 0 < (1: ℂ).re, by {norm_cast, exact zero_lt_one,},--simp only [nat.lt_one_iff],
  have h₁:= fourier_transform_gaussian_pi (h₀),
  rw mul_one at h₁,
  rw h₁,
  simp only [complex.one_cpow, div_one, one_mul],
end


lemma fourier_transform_eq_gaussian {x : ℝ}: 
real.fourier_integral gaussian_complex_pi.to_fun =gaussian_complex_pi.to_fun :=
begin
  have h₁:= fourier_transform_eq_gaussian2,
  exact funext h₁,
end


theorem fourier_transform_gaussian (x : ℝ) : 
∃ (f : ℝ → ℂ), f x = real.fourier_integral f x :=
begin
  use (λ (x : ℝ), cexp (-real.pi*x ^ 2)),
  have h₁:= fourier_transform_eq_gaussian,
  rw  [← gaussian_complex_to_fun, h₁, gaussian_complex_to_fun],
  exact x,
end


-- # The fourier transform of the gaussian is in the schwartz space 
def fourier_transform_gaussian_pi (x : ℝ) : schwartz_map ℝ ℂ:=
{ to_fun := λ x, real.fourier_integral gaussian_complex_pi.to_fun x,
  smooth' :=
  begin
    simp,
    have h₁:=  gaussian_complex_pi.smooth',
    rw fourier_transform_eq_gaussian,
    exact h₁,
    exact x,
  end,
  decay' :=
  begin
    simp,
    have h₁:=  gaussian_complex_pi.decay',
    rw fourier_transform_eq_gaussian,
    exact h₁,
    exact x,
  end}

localized "notation (name := fourier_integral) `𝓕` := real.fourier_integral" in fourier_transform


-- # We make usefull definitions
def fourier_convolution (f : schwartz_map ℝ ℂ) (g : schwartz_map ℝ ℂ) (x : ℝ) := ∫ (t: ℝ), f.to_fun (x-t) * g.to_fun t
def good_kernel {x δ : ℝ} (hδ : 0<δ) := λ x : ℝ, complex.exp (-((real.pi*δ) : ℂ)* ‖x‖^2)


-- # We formalize the multiplication formula
lemma multiplication_formula_step (f : ℝ → ℝ → ℂ) 
(ha : ∀ x : ℝ, measure_theory.integrable (f x) measure_theory.measure_space.volume)
(hb : measure_theory.integrable (λ (x : ℝ), ∫ (y : ℝ), ‖f x y‖) measure_theory.measure_space.volume)
(hc : continuous (function.uncurry f)) :
 ∫ (x : ℝ), ∫ (y : ℝ), f x y = ∫ (y : ℝ), ∫ (x : ℝ), f x y :=
begin
  convert measure_theory.integral_integral_swap _,
  exact measure_theory.measure.regular.sigma_finite,
  exact measure_theory.measure.regular.sigma_finite,
  simp only,
  rw measure_theory.integrable_prod_iff,
  split,
  refine eventually_of_forall _,
  intro x,
  simp_rw function.uncurry_apply_pair,
  refine ha x,
  simp_rw function.uncurry_apply_pair,
  refine hb,
  refine continuous.ae_strongly_measurable hc,
end


lemma continuous_cexp {x : ℝ} : continuous (λ (v : ℝ), cexp ((-2) * ↑real.pi * ↑v * ↑x * I)) :=
begin
  refine continuous.cexp  _,
  refine continuous.mul _ continuous_const,
  refine continuous.mul _ continuous_const,
  refine continuous.mul continuous_const _,
  refine continuous.comp of_real_clm.continuous continuous_id,
end


lemma integrable_exp_mul_schwartz2 (x : ℝ) (f : schwartz_map ℝ ℂ) :
measure_theory.integrable (λ (v : ℝ), (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * f.to_fun v) x) measure_theory.measure_space.volume:=
begin
  convert integrable_mul_schwartz_map _ (λ (v : ℝ), cexp ((-2) * ↑real.pi * ↑v * ↑x * I)) (integrable_schwartz_map (f)) _ _,
  ext1, dsimp only, repeat {rw ←neg_mul,},-- sorry,-- congr, sorry, rw pow_one,
  have h₂:=cexp_bound x,
  obtain ⟨C,h₂⟩:=h₂,
  use C,
  intro x, specialize h₂ x,
  convert h₂,
  norm_cast,
  refine continuous_cexp,
end


lemma rewrite_imaginary_part {x v : ℝ}: 
↑((-2) * real.pi * x * v) * I = -((2: ℂ) * (real.pi: ℂ) * (v : ℂ) * (x : ℂ) * I) :=
begin
  repeat {rw ← neg_mul,},
  norm_cast,
  rw [mul_assoc _ v x, mul_assoc _ x v, mul_comm x v],
end


lemma integrable_schwartz_mul_schwartz_mul_cexp {f g : schwartz_map ℝ ℂ}: 
∀ (x : ℝ), measure_theory.integrable ((λ (y x : ℝ), f.to_fun y * g.to_fun x * cexp (↑((-2) * real.pi * y * x) * I)) x) measure_theory.measure_space.volume :=
begin
  intro x,
  simp_rw mul_assoc _ (g.to_fun _) _,
  refine measure_theory.integrable.const_mul _ _,
  simp_rw mul_comm (g.to_fun _) _,
  convert integrable_exp_mul_schwartz2 x g, 
  ext1 v, congr, refine rewrite_imaginary_part,
end


lemma norm_schwartz_mul_schwartz_mul_cexp_eq {f g : schwartz_map ℝ ℂ}: 
(λ (x : ℝ), ∫ (y : ℝ), ‖f.to_fun x * g.to_fun y * cexp (↑((-2) * real.pi * x * y) * I)‖) = (λ (x : ℝ), (∫ (y : ℝ), ‖g.to_fun y‖)*(λ (x : ℝ),‖f.to_fun x‖) x) :=
begin
  ext1 w,
  have h₁: ∀y : ℝ,  ‖cexp (↑((-2) * real.pi * w * y) * I)‖ = 1,
    {intro y, rw complex.norm_exp_of_real_mul_I,},
  simp_rw [norm_mul, h₁, mul_one],
  rw [←smul_eq_mul, ← integral_smul_const],
  simp_rw [smul_eq_mul,mul_comm], 
end


lemma integrable_norm_schwartz_mul_schwartz_mul_cexp {f g : schwartz_map ℝ ℂ}: 
measure_theory.integrable (λ (x : ℝ), ∫ (y : ℝ), ‖(λ (y x : ℝ), f.to_fun y * g.to_fun x * cexp (↑((-2) * real.pi * y * x) * I)) x y‖) measure_theory.measure_space.volume:=
begin
  dsimp only,
  rw norm_schwartz_mul_schwartz_mul_cexp_eq,
  refine measure_theory.integrable.const_mul _ _,
  dsimp only,
  refine measure_theory.integrable.norm  _,
  exact integrable_schwartz_map _,
end


lemma continuous_uncurry_schwartz_mul_schwartz_mul_cexp {f g : schwartz_map ℝ ℂ}: 
continuous (function.uncurry (λ (y x : ℝ), f.to_fun y * g.to_fun x * cexp (↑((-2) * real.pi * y * x) * I))) :=
begin
  sorry, -- we had to sorry that the function was continuous
end


lemma multiplication_formula : 
∀  (f g : schwartz_map ℝ ℂ), ∫ (x : ℝ), (f.to_fun x) * (real.fourier_integral g.to_fun x) = ∫ (y : ℝ), (real.fourier_integral f.to_fun y) * (g.to_fun y) := 
begin
  intros f g,
  have h₁:= multiplication_formula_step (λ y : ℝ,(λ x : ℝ, f.to_fun y * g.to_fun x * cexp (↑((-2) * real.pi * y * x) * I))) _ _ _, 
  convert h₁,
  simp_rw fourier_integral_eq_integral_exp_smul g.to_fun _,
  ext1 x, rw [ mul_comm (f.to_fun x) _,← smul_eq_mul,← integral_smul_const],
  congr, ext1 y,
  repeat {rw smul_eq_mul,},
  ring_nf,
  simp_rw fourier_integral_eq_integral_exp_smul f.to_fun _,
  ext1 x, rw [← smul_eq_mul,← integral_smul_const],
  congr, ext1 y,
  repeat {rw smul_eq_mul,},
  ring_nf,
  exact integrable_schwartz_mul_schwartz_mul_cexp,
  exact integrable_norm_schwartz_mul_schwartz_mul_cexp,
  exact continuous_uncurry_schwartz_mul_schwartz_mul_cexp,
end


-- # We now prove that the fourier transform is a schwartz_map. Also a long proof. See line 1995
-- # We also formalize proposition_1_2_v during this

lemma deriv_cexp' {h : ℝ}: 
deriv (λ (y : ℝ), cexp (-(2 * ↑real.pi * ↑h * ↑y * I)))  = deriv (λ (y : ℝ), cexp ((↑((-2) * real.pi * h) * I)* y)) :=
begin 
  ext1 x,congr,ext1 y,repeat {rw ← neg_mul,}, rw [mul_comm _ I, mul_comm _ I], repeat {rw ← mul_assoc,},repeat {rw mul_assoc,},
  rw ← mul_assoc _ (h : ℂ) _, norm_cast, repeat {rw ← mul_assoc,},
end


lemma integral_deriv_rw (f : schwartz_map ℝ ℂ) {x : ℝ}: 
(λ (n : ℝ), ∫ (v : ℝ) in -n..n, deriv (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * f.to_fun v) x) = λ (n : ℝ), (∫ (v : ℝ) in -n..n,  (λ (w : ℝ), -(2 * ↑real.pi * ↑v * I) * cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * f.to_fun v) x) :=
begin
  ext1 n, congr, ext1 x, rw [deriv_mul_const,deriv_cexp',deriv_exp_neg_complex_mul], dsimp, rw neg_mul, congr,
  repeat {rw ← neg_mul,},congr,norm_cast, repeat {rw ← mul_assoc,}, repeat {rw ← neg_mul,},
  repeat {rw ← neg_mul,}, rw mul_comm _ I, rw mul_comm _ I, rw mul_assoc I _ _, 
  congr,norm_cast, 
  refine differentiable.differentiable_at _,
  refine differentiable.cexp _,
  refine differentiable.neg _,
  refine differentiable.mul_const _ _,
  refine differentiable.const_mul _ _,
  refine differentiable.comp _ differentiable_id,
  refine of_real_clm.differentiable,
end

lemma functions_equal_1 {f : schwartz_map ℝ ℂ} {x : ℝ}: 
(λ (v : ℝ), (λ (v : ℝ), ↑v * I * cexp ((-2) * ↑real.pi * ↑v * ↑x * I) * f.to_fun v) v) = λ (v : ℝ), I * (λ (v : ℝ), cexp ((-2) * ↑real.pi * ↑v * ↑x * I) * (↑v * f.to_fun v)) v :=
begin
  ext1 v,  dsimp,
  rw [mul_comm _ I,mul_assoc I _ _, mul_assoc I _ _, mul_comm (v : ℂ) _, mul_assoc _ (v : ℂ) _],
end

lemma functions_equal_2 {f : schwartz_map ℝ ℂ} {x : ℝ}: 
(λ (v : ℝ), (-2) * (real.pi: ℂ) * ↑v * I * cexp ((-2) * (real.pi: ℂ) * ↑v * ↑x * I) * (f.to_fun v)) =(λ (v : ℝ), ((-2) * (real.pi: ℂ)) * (λ (v : ℝ), ↑v * I * cexp ((-2) * (real.pi: ℂ) * ↑v * ↑x * I) * f.to_fun v) v) :=
begin
  ext1 v, dsimp, repeat{rw ← mul_assoc,},
end

lemma rewrite5 {a : ℂ}: 
(λ (x : ℝ),cexp (-(2 * ↑real.pi * ↑a * ↑x * I))) = (λ (x : ℝ),cexp (-(2 * ↑real.pi * ↑a  * I) * ↑x)) :=
begin
  ext1 x,
  congr,
  repeat {rw ← neg_mul,},
  rw [mul_assoc _ _ I, mul_comm _ I,← mul_assoc _ I _],
end

lemma ae_strongly_measurable_deriv_cexp_mul_schwartz {x : ℝ} {f : schwartz_map ℝ ℂ}:
measure_theory.ae_strongly_measurable (λ (a : ℝ), deriv (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑a * ↑w * I)) * f.to_fun a) x) measure_theory.measure_space.volume:=
begin
  refine continuous.ae_strongly_measurable _,
  simp only [deriv_mul_const_field'],
  refine continuous.mul _ (schwartz_map.continuous f),
  have h₁:(λ (a : ℝ), deriv (λ (x : ℝ), cexp (-(2 * ↑real.pi * ↑a * ↑x * I))) x)= (λ (a : ℝ), (λ (x : ℝ), -(2 * ↑real.pi * ↑a * I) * cexp (-(2 * ↑real.pi * ↑a * I) * ↑x)) x), 
    {ext1 a,
    have : (λ (x : ℝ),cexp (-(2 * ↑real.pi * ↑a * ↑x * I))) = (λ (x : ℝ),cexp (-(2 * ↑real.pi * ↑a  * I) * ↑x)), by refine rewrite5,
    rw [this, deriv_exp_neg_complex_mul _ _],},
  simp_rw h₁,
  refine continuous.mul (continuous.neg _) _,
  refine continuous.mul _ continuous_const,
  refine continuous.mul continuous_const _,
  refine continuous.comp of_real_clm.continuous continuous_id,
  convert continuous_cexp,
  ext1 a,
  repeat {rw ← neg_mul,},
  rw [mul_assoc _ I _, mul_comm I _,← mul_assoc _ _ I],
end

lemma ae_strongly_measurable_cexp_mul_schwartz {x : ℝ} {f : schwartz_map ℝ ℂ}: 
∀ᶠ (x : ℝ) in nhds x, measure_theory.ae_strongly_measurable ((λw : ℝ,(λv : ℝ,cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * f.to_fun v)) x) measure_theory.measure_space.volume:=
begin
  refine eventually_of_forall _, 
  intro x,
  refine continuous.ae_strongly_measurable _,
  dsimp only,
  refine continuous.mul _ (schwartz_map.continuous f),
  repeat {simp_rw ←neg_mul,},
  refine continuous_cexp,
end


lemma metric_ball_has_deriv_at  {x h : ℝ} (f : schwartz_map ℝ ℂ) : 
∀ᵐ (a : ℝ), ∀ (x_1 : ℝ), x_1 ∈ metric.ball x h → has_deriv_at (λ (x : ℝ), (λ (w v : ℝ), cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * f.to_fun v) x a) (deriv (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑a * ↑w * I)) * f.to_fun a) x_1) x_1:=
begin
  refine eventually_of_forall _, 
  intro x,
  intro y,
  intro hy,
  rw has_deriv_at_deriv_iff,
  dsimp,
  refine differentiable_at.mul _ (differentiable_at_const _),
  refine differentiable_at.cexp _,
  refine differentiable_at.neg _,
  refine differentiable_at.mul_const _ _,
  refine differentiable_at.const_mul _ _,
  refine differentiable_at.comp _ _ differentiable_at_id,
  refine of_real_clm.differentiable_at,
end


lemma cexp_mul_schwartz_moderate_decrease (f :schwartz_map ℝ ℂ) : 
∃ (C : ℝ), ∀ x : ℝ, ∀ᵐ (v : ℝ), ‖(cexp (↑((-2) * real.pi * v * x) * I) • (f.to_fun v))‖ ≤ (λ x : ℝ, (‖C‖ /(1 + ‖x‖^2))) v :=
begin
  have h₁:=moderate_decrease_pow f,
  specialize h₁ 0, 
  obtain ⟨C,h₁⟩:=h₁, 
  use C, 
  intro h, 
  refine eventually_of_forall _,  
  intro y, 
  specialize h₁ y, 
  rw [pow_zero,one_mul] at h₁,
  simp_rw [norm_smul _ _, complex.norm_exp_of_real_mul_I _, one_mul],  
  refine le_trans h₁ _, 
  refine div_le_div (norm_nonneg _) (real.le_norm_self _) _ rfl.ge, 
  positivity, 
end


lemma rewrite3 {C : ℝ} {n : ℕ}:
(λ (x : ℝ), ‖(-(2: ℂ)) ^ n‖ • ‖I ^ n‖ • ‖(real.pi: ℂ) ^ n‖ * (‖C‖ / (1 + ‖x‖ ^ 2)))  =(λ (x : ℝ), ((‖(-(2: ℂ)) ^ n‖ • ‖I ^ n‖ • ‖(real.pi: ℂ) ^ n‖ * ‖C‖) / (1 + ‖x‖ ^ 2))) :=
begin
  ext1 x, rw div_eq_mul_one_div, nth_rewrite_rhs 0 div_eq_mul_one_div, repeat {rw ← mul_assoc,},
end 


lemma integral_moderate_decrease_bounded {C : ℝ} (l:filter ℝ) :
∃ I: ℝ,  ∀ᶠ (i : ℝ) in l, ∫ (x : ℝ) in (λ y : ℝ ,-‖y‖) i..(λ y : ℝ ,‖y‖) i, ‖(λ (x : ℝ), C / (1 + ‖x‖ ^ 2)) x‖ ≤ I:=
begin
  set a := (λ y : ℝ ,-‖y‖) with ha,
  set b := (λ y : ℝ ,‖y‖) with hb,
  use (((real.pi/2+1)+(real.pi/2+1))*‖C‖),
  refine filter.eventually_of_forall _,
  intro i,
  have h₁: ∫ (x : ℝ) in a i..b i, ‖(λ (x : ℝ), C / (1 + ‖x‖ ^ 2)) x‖ = (∫ (x : ℝ) in a i..b i, 1 / (1 + x ^ 2))*‖C‖, 
  {rw [←smul_eq_mul,←  interval_integral.integral_smul_const], congr, ext1,
   rw [norm_div, div_eq_mul_one_div, mul_comm, smul_eq_mul],congr,
   simp only [norm_eq_abs, pow_bit0_abs, abs_eq_self],positivity,},
  rw [h₁, integral_one_div_one_add_sq, sub_eq_add_neg],
  refine mul_le_mul _ rfl.ge (norm_nonneg _) _,
  refine add_le_add _ _,
  refine le_trans (le_of_lt (arctan_lt_pi_div_two (b i))) _,
  simp only [le_add_iff_nonneg_right, zero_le_one],
  {rw neg_le,  refine le_trans _ (le_of_lt (real.neg_pi_div_two_lt_arctan (a i))),
  refine neg_le_neg _,  simp only [le_add_iff_nonneg_right, zero_le_one],},
  have h₃: real.pi / 2 + 1 + (real.pi / 2 + 1) = 2*(real.pi / 2 + 1), rw two_mul,
  rw [h₃, zero_le_mul_right zero_lt_pi_div_two_pos_plus_one],
  exact zero_le_two,
end


lemma integrable_moderate_decrease (C : ℝ) : 
measure_theory.integrable (λ (v : ℝ), (λ (x : ℝ), (C / (1 + ‖x‖ ^ 2))) v) measure_theory.measure_space.volume:=
begin
  have h := integral_moderate_decrease_bounded at_top, 
  obtain ⟨I,h⟩:=h,
  refine measure_theory.integrable_of_interval_integral_norm_bounded I _ _ _ h,
  {intro i,
  refine continuous.integrable_on_Ioc _,
  refine continuous.div continuous_const _ _,
  refine continuous.add continuous_const _,
  refine continuous.pow _ 2,
  refine continuous_norm,
  intro x, symmetry, positivity,},
  {simp only [tendsto_neg_at_bot_iff], exact tendsto_norm_at_top_at_top,},
  {exact tendsto_norm_at_top_at_top,},
end


lemma deriv_cexp_bound_explicit (h : ℝ) : 
 ∀ (x : ℝ), ‖deriv (λ (y : ℝ), cexp (↑((-2) * real.pi * y * h) * I)) x‖ ≤ 2 * |real.pi|* ‖h‖:=
begin
  intro x,
  simp only [neg_mul, of_real_neg, of_real_mul, of_real_bit0, of_real_one],
  rw [norm_deriv_rw, deriv_exp_neg_complex_mul (↑((-2) * real.pi * h) * I) x],
  simp only [neg_mul, of_real_neg, of_real_mul, of_real_bit0, of_real_one, complex.norm_eq_abs, absolute_value.map_neg,
  absolute_value.map_mul, complex.abs_two, abs_of_real, abs_I, mul_one],
  have h₂: ‖cexp (-(2 * ↑real.pi * ↑h * I * ↑x))‖ = ‖cexp ((↑(-2 * real.pi *h * x))* I)‖,
  {congr,repeat {rw ← neg_mul,}, rw [mul_comm _ I, mul_comm _ I], repeat {rw mul_assoc,}, congr, norm_cast,},
  rw [← complex.norm_eq_abs,h₂, complex.norm_exp_of_real_mul_I _, mul_one, real.norm_eq_abs],
end


lemma bound_one_div_one_add_sq {x : ℝ} : ‖x‖/(1+ ‖x‖*(1+ ‖x‖^2)) ≤ 1/((1+ ‖x‖^2)) :=
begin
  cases le_or_lt (‖x‖) 1,
  refine div_le_div zero_le_one h _ _,
  positivity,
  refine add_le_add rfl.ge _,
  rw sq,
  refine mul_le_mul rfl.ge _ (norm_nonneg _) (norm_nonneg _),
  refine le_trans h _,
  simp only [le_add_iff_nonneg_right],
  positivity,
  have h₁: 1 / (1 + ‖x‖ ^ 2) = ‖x‖ / (‖x‖ *(1 + ‖x‖ ^ 2)), 
  rw [div_mul_eq_div_mul_one_div, div_self _, one_mul],
  positivity,
  rw h₁,
  refine div_le_div (norm_nonneg _) rfl.ge _ _,
  positivity,
  rw [mul_add, mul_one],
  simp only [le_add_iff_nonneg_left, zero_le_one],
end

lemma moderate_decrease_pow_bounded_const_div_one_add_norm_mul_one_add_sq (f : schwartz_map ℝ ℂ) :
∀ k : ℕ, ∃ C : ℝ, ∀ x : ℝ, ‖x‖^k * ‖f.to_fun x‖ ≤  (C)/(1+ ‖x‖*(1+ ‖x‖^2)) :=
begin
  intro k,
  have h₁:= f.decay',  have h₂:= f.decay',  have h₃:= f.decay',
  specialize h₁ (k),  specialize h₂ (k+1), specialize h₃ (k+3),
  specialize h₁ 0,  specialize h₂ 0, specialize h₃ 0,
  obtain ⟨C₁,h₁⟩:=h₁,  obtain ⟨C₂,h₂⟩:=h₂,  obtain ⟨C₃,h₃⟩:=h₃,
  use (C₁ + C₂ + C₃),
  intro x,
  rw [le_div_iff _, mul_add, mul_add, mul_add, mul_one, mul_one],
  nth_rewrite 2 ← pow_one (‖x‖),
  nth_rewrite 4 ← pow_one (‖x‖),
  rw [← pow_add _ _, ← add_assoc],
  nth_rewrite 1 mul_comm _ (‖f.to_fun x‖),
  nth_rewrite 1 mul_comm _ (‖f.to_fun x‖),
  refine add_le_add (add_le_add _ _) _,
  {specialize h₁ x,  
  simp only [norm_iterated_fderiv_zero] at h₁, 
  refine h₁,},
  {rw [mul_assoc, ← pow_add _ _, mul_comm],
  specialize h₂ x, 
  simp only [norm_iterated_fderiv_zero] at h₂,
  refine h₂,},
  {have h₄: 1 + 2 = 3, ring_nf,
  rw [h₄, mul_assoc, ← pow_add _ _, mul_comm],
  specialize h₃ x,
  simp only [norm_iterated_fderiv_zero] at h₃,
  refine h₃,},
  {positivity,},
end


lemma rewrite_bound {y C₁: ℝ} (h : 0 ≤ C₁) : 
(2 * (|real.pi|) * ‖y‖) * ((C₁)/(1+ ‖y‖*(1+ ‖y‖^2))) ≤ C₁ * 2 * (|real.pi| / (1 + ‖y‖ ^ 2)) :=
begin
  rw div_eq_mul_one_div,
  rw ← mul_assoc,
  rw mul_assoc _ (‖y‖) _,
  rw mul_comm (‖y‖) _,
  repeat {rw ← mul_assoc,},
  rw mul_assoc,
  rw ← div_eq_mul_one_div,
  nth_rewrite 1 div_eq_mul_one_div,
  repeat {rw ← mul_assoc,},
  refine mul_le_mul _ _ _ _,
  rw mul_comm _ C₁,
  rw mul_assoc,
  exact bound_one_div_one_add_sq,
  positivity,
  positivity,
end


lemma deriv_cexp_mul_schwartz_moderate_decrease (f :schwartz_map ℝ ℂ) : 
∀ x : ℝ, ∃ (C : ℝ), ∀ᵐ (a : ℝ), ∀ (x_1 : ℝ), x_1 ∈ metric.ball x (‖C‖+1) → ‖deriv (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑a * ↑w * I)) * f.to_fun a) x_1‖ ≤ (C) / (1 + ‖a‖ ^ 2) :=
begin
   have h₁:=moderate_decrease_pow_bounded_const_div_one_add_norm_mul_one_add_sq f,
  specialize h₁ 0, 
  intro x, 
  obtain ⟨C₁,h₁⟩:=h₁,
  use (C₁*2 * |real.pi|), 
  refine eventually_of_forall _,  
  intro y,  intros w hw,
  have h₂:= deriv_cexp_bound_explicit y,
  specialize h₁ y, 
  specialize h₂ w, 
  rw [pow_zero,one_mul] at h₁,
  simp only [deriv_mul_const_field', norm_mul, pow_bit0_abs],
  rw mul_div_assoc,
  --have h₃: (2 * (|real.pi|) * ‖y‖) * ((C₁)/(1+ ‖y‖*(1+ ‖y‖^2))) ≤ C₁ * 2 * (|real.pi| / (1 + ‖y‖ ^ 2)), sorry,
  refine le_trans _ (rewrite_bound _),
  convert mul_le_mul h₂ h₁ _ _,
  ext1 b,
  repeat {rw ←neg_mul,},
  rw [mul_comm _ I, mul_comm _ I],
  congr,
  norm_cast,
  rw [mul_assoc _ b _, mul_assoc _ _ b, mul_comm _ b],
  positivity,
  positivity,
  rw le_div_iff _ at h₁,
  refine le_trans _ h₁,
  positivity,
  positivity,
end


lemma has_deriv_fourier_transform  {x : ℝ} {f : schwartz_map ℝ ℂ}: 
has_deriv_at (λ (n : ℝ), ∫ (v : ℝ), cexp (-(2 * ↑real.pi * ↑v * ↑n * I)) * f.to_fun v) (∫ (a : ℝ), deriv (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑a * ↑w * I)) * f.to_fun a) x) x :=
begin
  have h₁:  ∀ᶠ (x : ℝ) in nhds x, measure_theory.ae_strongly_measurable ((λw : ℝ,(λv : ℝ,cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * f.to_fun v)) x) measure_theory.measure_space.volume,
    refine ae_strongly_measurable_cexp_mul_schwartz,
  have h₂:  measure_theory.ae_strongly_measurable (λ (a : ℝ), deriv (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑a * ↑w * I)) * f.to_fun a) x) measure_theory.measure_space.volume, 
    refine ae_strongly_measurable_deriv_cexp_mul_schwartz,
  have h₄:= deriv_cexp_mul_schwartz_moderate_decrease f x,
  obtain ⟨C,h₄⟩:=h₄,
  have h₃:= has_deriv_at_integral_of_dominated_loc_of_deriv_le _ h₁ (integrable_exp_mul_schwartz2 _ _) h₂ _ _ _,
  dsimp at h₃,
  refine h₃.2,
  use (‖C‖+1),
  positivity,
  use (λ (x : ℝ), (C)/ (1 + ‖x‖ ^ 2)),
  refine h₄,
  refine integrable_moderate_decrease _,
  refine metric_ball_has_deriv_at _,
end 


lemma leibniz_rule (f : schwartz_map ℝ ℂ) (x : ℝ) : 
deriv (λ (w : ℝ), ∫ (v : ℝ), cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * f.to_fun v) x =  ∫ (v : ℝ), deriv (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * f.to_fun v) x :=
begin
  convert has_deriv_at.deriv has_deriv_fourier_transform,
end


lemma cont_diff_pow_mul_schwartz {n : ℕ} {f :schwartz_map ℝ ℂ}: 
cont_diff ℝ ⊤ (λ (x : ℝ), (↑x) ^ n * f.to_fun x) :=
begin
  refine cont_diff.mul _ f.smooth',
  refine cont_diff.pow _ n,
  refine cont_diff.comp _ _,
  exact of_real_clm.cont_diff,
  exact cont_diff_id,
end


lemma cont_diff_const_pow_mul_schwartz {n : ℕ} {f :schwartz_map ℝ ℂ} {a : ℂ}: 
cont_diff ℝ ⊤ (λ (x : ℝ), (a * ↑x) ^ n * f.to_fun x) :=
begin
  simp_rw [mul_pow, mul_assoc],
  refine cont_diff.mul cont_diff_const cont_diff_pow_mul_schwartz,
end


def const_pow_mul_schwartz_map  (n : ℕ) (f :schwartz_map ℝ ℂ) : schwartz_map ℝ ℂ :=
{ to_fun :=λ (x : ℝ), ((-2) * ↑real.pi * I * ↑x) ^ n * f.to_fun x,
smooth' := cont_diff_const_pow_mul_schwartz,
decay' := 
begin
  intros k m,
  have h := (schwartz_mul_x_pow n f).decay',
  specialize h k, specialize h m,
  obtain ⟨C,h⟩:=h,
  use (‖(-2) ^ n * ↑real.pi ^ n * I ^ n‖*C),
  intro x, specialize h x,
  have h₁: (λ (x : ℝ), (-2) ^ n * ↑real.pi ^ n * I ^ n * ↑x ^ n * f.to_fun x) = ((-2) ^ n * ↑real.pi ^ n * I ^ n) • (λ (x : ℝ), ↑x ^ n * f.to_fun x),
  {ext1 x,  dsimp, rw ← mul_assoc _ ((x : ℂ)^n) _,},
  simp_rw [mul_pow, h₁],
  rw [iterated_fderiv_const_smul_apply  _, norm_smul, mul_comm, mul_assoc],
  refine mul_le_mul rfl.ge _ _ (norm_nonneg _),
  rw mul_comm,
  convert h,
  positivity,
  have hm : ↑m ≤ (⊤ : ℕ∞), by {refine le_of_lt _, exact with_top.coe_lt_top m,},
  refine cont_diff.of_le cont_diff_pow_mul_schwartz hm,
end ,}


lemma iterated_deriv_cexp_eq_mul_pow_cexp {f : schwartz_map ℝ ℂ} {n : ℕ} {v : ℝ}:
∀ x : ℝ,  iterated_deriv n (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * f.to_fun v) x = (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑v * ↑w * I))* (-2* ↑real.pi*I*v)^n* f.to_fun v) x :=
begin
  induction n with n hn, 
  intro x,
  simp only [iterated_deriv_zero, pow_zero, mul_one],
  intro x,
  rw iterated_deriv_succ,
  have h₁:= funext hn,
  dsimp only at h₁,
  simp_rw [h₁],
  simp only [neg_mul, deriv_mul_const_field', mul_eq_mul_right_iff],
  left,
  have h₂:(λ (x : ℝ), cexp (-(2 * ↑real.pi * ↑v * ↑x * I)))= (λ (x : ℝ), cexp (-(2 * ↑real.pi *I *  ↑v)* ↑x)), by {ext1,ring_nf,},
  have h₃: cexp (-(2 * ↑real.pi * ↑v * ↑x * I)) = (λ (x : ℝ),cexp (-(2 * ↑real.pi * ↑v * ↑x * I)))  x, by {dsimp only, congr,},
  rw [h₂, deriv_exp_neg_complex_mul _, nat.succ_eq_add_one, pow_add], 
  dsimp only,
  rw [mul_comm _ (cexp(_)), pow_one,mul_comm ((-(2 * (real.pi: ℂ) *I *↑v)) ^ n) _,   mul_assoc (cexp(_)) _ _,h₃, h₂],
end


lemma leibniz_rule_induction {f : schwartz_map ℝ ℂ} {n : ℕ}: 
∀ x : ℝ, iterated_deriv n (λ (w : ℝ), ∫ (v : ℝ), cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * f.to_fun v) x =  ∫ (v : ℝ), iterated_deriv n (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * f.to_fun v) x :=
begin
  induction n with n hn, 
  {intro x,
  simp only [iterated_deriv_zero],},
  {rw iterated_deriv_succ,
  intro x,
  have h₁:= funext hn,
  dsimp only at h₁,
  simp_rw [h₁,iterated_deriv_cexp_eq_mul_pow_cexp],
  have h₁:= leibniz_rule (const_pow_mul_schwartz_map n f) x,
  have h₂: (const_pow_mul_schwartz_map n f).to_fun =λ (x : ℝ), ((-2) * ↑real.pi * I * ↑x) ^ n * f.to_fun x, refl,
  have h₃: deriv (λ (w : ℝ), ∫ (v : ℝ), cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * (const_pow_mul_schwartz_map n f).to_fun v) x = deriv (λ (w : ℝ), ∫ (v : ℝ), cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * (-2* ↑real.pi* I* v)^n* f.to_fun v) x,
  {congr,  ext1 w,  congr,  ext1 v,
  rw mul_assoc _ _ (f.to_fun v), congr,},
  rw [← h₃,h₁],
  congr,
  simp only [deriv_mul_const_field', neg_mul],
  ext1 y,
  have h₄:deriv (λ (x : ℝ), cexp (-(2 * ↑real.pi * ↑y * ↑x * I))) x= deriv (λ (x : ℝ), cexp (-(2 * ↑real.pi *I *  ↑y)* ↑x)) x, by {congr,ext1,ring_nf,},
  rw [h₄, deriv_exp_neg_complex_mul _, nat.succ_eq_add_one, pow_add], 
  dsimp only,
  rw [mul_comm _ (cexp(_)), pow_one,mul_comm ((-(2 * (real.pi: ℂ) *I *↑y)) ^ n) _, 
  mul_assoc (cexp(_)) _ _, mul_assoc (cexp(_)) _ _, mul_assoc _ _ (f.to_fun y)],
  repeat {rw ←neg_mul,},
  rw [mul_assoc _ _ (x : ℂ), mul_comm _ (x : ℂ),← mul_assoc _ (x : ℂ) _,h₂],
  dsimp,
  nth_rewrite 0 mul_assoc _ _ (y : ℂ), 
  nth_rewrite 0 mul_assoc _ _ ((x : ℂ)*(y : ℂ)),
  nth_rewrite 0 mul_comm (x : ℂ) (y : ℂ),
  nth_rewrite 0 mul_comm _ ((y : ℂ)*(x : ℂ)),
  repeat {rw ← mul_assoc,},},
end


lemma has_iterated_deriv_fourier_transform  {x : ℝ} {f : schwartz_map ℝ ℂ}: 
has_deriv_at (λ (n : ℝ), ∫ (v : ℝ), cexp (-(2 * ↑real.pi * ↑v * ↑n * I)) * f.to_fun v) (∫ (a : ℝ), deriv (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑a * ↑w * I)) * f.to_fun a) x) x :=
begin
  have h₁:  ∀ᶠ (x : ℝ) in nhds x, measure_theory.ae_strongly_measurable ((λw : ℝ,(λv : ℝ,cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * f.to_fun v)) x) measure_theory.measure_space.volume,
    refine ae_strongly_measurable_cexp_mul_schwartz,
  have h₂:  measure_theory.ae_strongly_measurable (λ (a : ℝ), deriv (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑a * ↑w * I)) * f.to_fun a) x) measure_theory.measure_space.volume, 
    refine ae_strongly_measurable_deriv_cexp_mul_schwartz,
  have h₄:= deriv_cexp_mul_schwartz_moderate_decrease f x,
  obtain ⟨C,h₄⟩:=h₄,
  have h₃:= has_deriv_at_integral_of_dominated_loc_of_deriv_le _ h₁ (integrable_exp_mul_schwartz2 _ _) h₂ _ _ _,
  dsimp at h₃,
  refine h₃.2,
  use (‖C‖+1),
  positivity,
  use (λ (x : ℝ), (C)/ (1 + ‖x‖ ^ 2)),
  refine h₄,
  refine integrable_moderate_decrease _,
  refine metric_ball_has_deriv_at _,
end 


lemma integral_deriv_cexp' (f : schwartz_map ℝ ℂ) {x : ℝ}:  
∫ (v : ℝ), deriv (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * f.to_fun v) x =  (∫ (v : ℝ),  (λ (w : ℝ), -(2 * ↑real.pi * ↑v * I) * cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * f.to_fun v) x) :=
begin
  congr, ext1 x, rw [deriv_mul_const,deriv_cexp',deriv_exp_neg_complex_mul], dsimp, rw neg_mul, congr,
  repeat {rw ← neg_mul,},congr,norm_cast, repeat {rw ← mul_assoc,}, repeat {rw ← neg_mul,},
  repeat {rw ← neg_mul,}, rw mul_comm _ I, rw mul_comm _ I, rw mul_assoc I _ _, 
  congr,norm_cast, 
  refine differentiable.differentiable_at _,
  refine differentiable.cexp _,
  refine differentiable.neg _,
  refine differentiable.mul_const _ _,
  refine differentiable.const_mul _ _,
  refine differentiable.comp _ differentiable_id,
  refine of_real_clm.differentiable,
end


lemma fourier_integral_eq_integral_exp_smul_funext (f : schwartz_map ℝ ℂ) : 𝓕 f.to_fun = λ (w : ℝ), ∫ (v : ℝ), cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * f.to_fun v :=
begin
  have h := funext (fourier_integral_eq_integral_exp_smul f.to_fun),
  simp at h,  refine h,
end


lemma proposition_1_2_v {x : ℝ} (f : schwartz_map ℝ ℂ) : 
real.fourier_integral (λ (x : ℝ), ((-2*real.pi*I*x) : ℂ)*(f.to_fun x)) (x) = deriv (real.fourier_integral f.to_fun) x :=
begin 
  rw fourier_integral_eq_integral_exp_smul,
  rw [fourier_integral_eq_integral_exp_smul_funext, leibniz_rule, integral_deriv_cexp'],
  congr,  ext1 v,  dsimp only,
  repeat {rw ← neg_mul,},
  rw [mul_comm _ (cexp(_)),mul_assoc (cexp(_)) _ _, smul_eq_mul],
  rw [mul_assoc ((-2) * (real.pi: ℂ)) I v, mul_comm I v, ← mul_assoc ((-2) * (real.pi: ℂ)) v I],
  congr,
  norm_cast,
end


def f_mul {f : schwartz_map ℝ ℂ} {m : ℕ}: schwartz_map ℝ ℂ :=
{ to_fun := λ (x : ℝ), ((-2) * ↑real.pi * I * ↑x) ^ m * ((f.to_fun x) : ℂ),
  smooth' :=
  begin
    refine cont_diff.mul _ _,
    refine cont_diff.pow _ _,
    refine cont_diff.mul _ _,
    exact cont_diff_const,
    refine cont_diff.comp _ _,
    exact of_real_clm.cont_diff,
    exact cont_diff_id,
    exact f.smooth',
  end,
  decay' := 
  begin
    have h₁:= (schwartz_mul_x_pow m f).decay',
    intros k n,
    specialize h₁ k,
    specialize h₁ n,
    obtain ⟨C,h₁⟩:=h₁,
    use (‖((-2) * (real.pi: ℂ) * I)^m‖* C),
    intro x,
    specialize h₁ x,
    have h₂: (λ (x : ℝ), ((-2) * ↑real.pi * I * ↑x) ^ m * f.to_fun x) = ((-2) * ↑real.pi * I)^m • (λ (x : ℝ), (↑x) ^ m * f.to_fun x), by {ext1,rw [mul_pow,mul_assoc],congr,},
    rw [h₂, iterated_fderiv_const_smul_apply, norm_smul, ← mul_assoc, mul_comm (‖x‖ ^ k), mul_assoc],
    refine mul_le_mul (rfl.ge) _ _ (norm_nonneg _),
    have h₃: (schwartz_mul_x_pow m f).to_fun = λ x : ℝ , (x : ℂ)^m* f.to_fun x, by refl,
    rw h₃ at h₁,
    exact h₁,
    positivity,
    have hn : ↑n ≤ (⊤ : ℕ∞), by {exact le_of_lt (with_top.coe_lt_top n),},
    exact cont_diff.of_le (schwartz_mul_x_pow m f).smooth' hn,
  end ,}


lemma proposition_1_2_v_iterated (n : ℕ) (f : schwartz_map ℝ ℂ) :  ∀ (x : ℝ), iterated_deriv n (real.fourier_integral f.to_fun) x = real.fourier_integral (λ (x : ℝ), ((-2*real.pi*I*x) : ℂ)^n*(f.to_fun x)) (x) :=
begin
  induction n with n hn,
  intro x,
  simp only [iterated_deriv_zero, pow_zero, one_mul],
  rw iterated_deriv_succ,
  have h₁:= funext hn,
  dsimp at h₁, 
  rw h₁,
  intro x,
  have h₂:= proposition_1_2_v f_mul,
  have h₃: f_mul.to_fun = λ (x : ℝ), ((-2) * ↑real.pi * I * ↑x) ^ n * ((f.to_fun x) : ℂ), by refl,
  rw h₃ at h₂,
  rw ← h₂,
  dsimp,
  rw nat.succ_eq_add_one, 
  congr,
  ring_exp,
end


lemma n_top_integral_real (f : ℝ → ℝ) (hf : measure_theory.integrable (λ (v : ℝ), f v) measure_theory.measure_space.volume) :
tendsto (λ (n : ℝ), ∫ (v : ℝ) in -n..n, f v) at_top (nhds (∫ (v : ℝ), f v)) :=
begin
  refine measure_theory.interval_integral_tendsto_integral hf _ rfl.ge,
  {simp only [tendsto_neg_at_bot_iff], exact rfl.ge,},
end


lemma tendsto_arctan_at_top : tendsto (λ (k : ℝ), arctan k) at_top (nhds (real.pi / 2)) :=
begin
  simp_rw arctan,
  apply tendsto.comp _ (order_iso.tendsto_at_top _),
  sorry, -- a small sorry
end


lemma tendsto_nhds_unique_le {a b : ℝ} {f : ℝ  → ℝ} {l : filter ℝ} [ne_bot l]
(ha : tendsto f l (nhds a)) (hb : tendsto f l (nhds b)) : a ≤  b :=
begin
  rw le_iff_lt_or_eq,
  right,
  refine tendsto_nhds_unique ha hb,
end


lemma cexp_mul_schwartz_bounded(f :schwartz_map ℝ ℂ) : 
∃ (C : ℝ), ∀ x : ℝ, ‖∫ (v : ℝ), cexp (↑((-2) * real.pi * v * x) * I) • (f.to_fun v)‖ ≤ C :=
begin
  have h₂:= cexp_mul_schwartz_moderate_decrease f,
  obtain ⟨C,h₂⟩:=h₂,
  use ((‖C‖ + ‖C‖) • (real.pi / 2)),
  intro x, 
  specialize h₂ x,
  refine le_trans (measure_theory.norm_integral_le_of_norm_le _ h₂) _,
  simp_rw rewrite3,
  refine integrable_moderate_decrease _,
  have h₃: tendsto (λn : ℝ, ∫ (v : ℝ) in -n .. n, (λ x : ℝ, ‖C‖ / (1 + ‖x‖ ^ 2)) v) at_top (nhds(∫ (x : ℝ), (λ x : ℝ, ‖C‖ / (1 + ‖x‖ ^ 2)) x)),
    refine n_top_integral_real (λ x : ℝ, ‖C‖ / (1 + ‖x‖ ^ 2)) _,
    refine integrable_moderate_decrease _,
  refine tendsto_nhds_unique_le h₃ _,
  have h₄: (λ (n : ℝ),(∫ (x : ℝ) in -(n : ℝ)..(n : ℝ), ‖C‖ / (1 + ‖x‖ ^ 2)))= (λ (n : ℝ),((∫ (x : ℝ) in -(n : ℝ)..(n : ℝ), (1 + x ^ 2)⁻¹) * (‖C‖))),
    {ext1 n,rw [←smul_eq_mul,←  interval_integral.integral_smul_const], congr, ext1,
    rw [div_eq_mul_one_div, mul_comm, ← smul_eq_mul,inv_eq_one_div],
    simp only [norm_eq_abs, pow_bit0_abs],},
  rw [h₄],
  simp_rw [integral_inv_one_add_sq, sub_eq_add_neg, smul_eq_mul,mul_comm (‖C‖ + ‖C‖) _, add_mul _ _ (‖C‖)], 
  rw [mul_add],
  refine filter.tendsto.add _ _,
  refine filter.tendsto.mul_const _ tendsto_arctan_at_top,
  refine filter.tendsto.mul_const _ _,
  simp_rw [real.arctan_neg _,neg_neg],
  refine tendsto_arctan_at_top,
end


lemma fourier_transform_decay (f :schwartz_map ℝ ℂ) :  
∀ (k n : ℕ), ∃ (C : ℝ), ∀ (x : ℝ), ‖x‖ ^ k * ‖iterated_fderiv ℝ n (λ (ξ : ℝ), 𝓕 f.to_fun ξ) x‖ ≤ C :=
begin
  simp,
  intros k n,
  have h₁:=  (schwartz_const_mul ((-(2: ℂ)) ^ n * (real.pi: ℂ) ^ n * I ^ n) (schwartz_mul_x_pow n f)).decay',
  specialize h₁ 0, 
  specialize h₁ (n-1),
  have h₉:=cexp_mul_schwartz_bounded (schwartz_iterated_deriv k (schwartz_const_mul ((-(2: ℂ)) ^ n * (real.pi: ℂ) ^ n * I ^ n) (schwartz_mul_x_pow n f))),
  obtain ⟨C,h₉⟩:=h₉,
  obtain ⟨C₁,h₁⟩:=h₁,
  use (‖(1 / (2 * ↑real.pi * I)) ^ k‖*C),
  intro x,
  rw iterated_fderiv_eq_equiv_comp,
  simp only [linear_isometry_equiv.norm_map],
  have h₅:= proposition_1_2_v_iterated (n) f, 
  rw h₅ x,
  have h : ‖x ^ k‖ = ‖(x : ℂ) ^ k‖, by norm_cast,
  rw [← norm_eq_abs, ← norm_pow,h, ← norm_mul],
  have h₇:= proposition_1_2_iv_iterated_lemma k (const_pow_mul_schwartz_map n f),
  have h₁₀: (const_pow_mul_schwartz_map n f).to_fun = λ (x : ℝ), ((-2) * ↑real.pi * I * ↑x) ^ n * f.to_fun x, by refl,
  rw h₁₀ at h₇,
  rw ← h₇ x,
  rw norm_mul,
  simp_rw mul_pow,
  have h₈:(schwartz_const_mul ((-2) ^ n * ↑real.pi ^ n * I ^ n) (schwartz_mul_x_pow n f)).to_fun= λ x : ℝ , ((-2: ℂ) ^ n * ↑real.pi ^ n * I ^ n)* ((x : ℂ) ^ n * f.to_fun x), by refl,
  specialize h₁ x, specialize h₉ x,
  rw [h₈,pow_zero,one_mul] at h₁,
  refine mul_le_mul rfl.ge _ (norm_nonneg _) (norm_nonneg _), 
  convert h₉,
  rw fourier_integral_eq_integral_exp_smul _,
  congr, ext1 v, congr, ext1 x, rw mul_assoc _ ((x : ℂ) ^ n) _,  congr,
end


lemma has_deriv_leibniz {f : schwartz_map ℝ ℂ} {n : ℕ}: 
∀ x : ℝ, iterated_deriv n (λ (w : ℝ), ∫ (v : ℝ), cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * f.to_fun v) x =  ∫ (v : ℝ), iterated_deriv n (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * f.to_fun v) x :=
begin
  induction n with n hn, 
  {intro x,
  simp only [iterated_deriv_zero],},
  {rw iterated_deriv_succ,
  intro x,
  have h₁:= funext hn,
  dsimp only at h₁,
  simp_rw [h₁,iterated_deriv_cexp_eq_mul_pow_cexp],
  have h₁:= leibniz_rule (const_pow_mul_schwartz_map n f) x,
  have h₂: (const_pow_mul_schwartz_map n f).to_fun =λ (x : ℝ), ((-2) * ↑real.pi * I * ↑x) ^ n * f.to_fun x, refl,
  have h₃: deriv (λ (w : ℝ), ∫ (v : ℝ), cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * (const_pow_mul_schwartz_map n f).to_fun v) x = deriv (λ (w : ℝ), ∫ (v : ℝ), cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * (-2* ↑real.pi* I* v)^n* f.to_fun v) x,
  {congr,  ext1 w,  congr,  ext1 v,
  rw mul_assoc _ _ (f.to_fun v), congr,},
  rw [← h₃,h₁],
  congr,
  simp only [deriv_mul_const_field', neg_mul],
  ext1 y,
  have h₄:deriv (λ (x : ℝ), cexp (-(2 * ↑real.pi * ↑y * ↑x * I))) x= deriv (λ (x : ℝ), cexp (-(2 * ↑real.pi *I *  ↑y)* ↑x)) x, by {congr,ext1,ring_nf,},
  rw [h₄, deriv_exp_neg_complex_mul _, nat.succ_eq_add_one, pow_add], 
  dsimp only,
  rw [mul_comm _ (cexp(_)), pow_one,mul_comm ((-(2 * (real.pi: ℂ) *I *↑y)) ^ n) _, 
  mul_assoc (cexp(_)) _ _, mul_assoc (cexp(_)) _ _, mul_assoc _ _ (f.to_fun y)],
  repeat {rw ←neg_mul,},
  rw [mul_assoc _ _ (x : ℂ), mul_comm _ (x : ℂ),← mul_assoc _ (x : ℂ) _,h₂],
  dsimp,
  nth_rewrite 0 mul_assoc _ _ (y : ℂ), 
  nth_rewrite 0 mul_assoc _ _ ((x : ℂ)*(y : ℂ)),
  nth_rewrite 0 mul_comm (x : ℂ) (y : ℂ),
  nth_rewrite 0 mul_comm _ ((y : ℂ)*(x : ℂ)),
  repeat {rw ← mul_assoc,},},
end


lemma ae_strongly_measurable_cexp_mul_schwartz2 {x : ℝ} (f : schwartz_map ℝ ℂ) :  
∀ᶠ (x : ℝ) in nhds x, measure_theory.ae_strongly_measurable ((λw : ℝ,(λv : ℝ,cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * f.to_fun v)) x) measure_theory.measure_space.volume:=
begin
  refine eventually_of_forall _, 
  intro x,
  refine continuous.ae_strongly_measurable _,
  dsimp only,
  refine continuous.mul _ (schwartz_map.continuous f),
  repeat {simp_rw ←neg_mul,},
  refine continuous_cexp,
end


lemma ae_strongly_measurable_deriv_cexp_mul_schwartz2 {x : ℝ} (f : schwartz_map ℝ ℂ) :
measure_theory.ae_strongly_measurable (λ (a : ℝ), deriv (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑a * ↑w * I)) * f.to_fun a) x) measure_theory.measure_space.volume:=
begin
  refine continuous.ae_strongly_measurable _,
  simp only [deriv_mul_const_field'],
  refine continuous.mul _ (schwartz_map.continuous f),
  have h₁:(λ (a : ℝ), deriv (λ (x : ℝ), cexp (-(2 * ↑real.pi * ↑a * ↑x * I))) x)= (λ (a : ℝ), (λ (x : ℝ), -(2 * ↑real.pi * ↑a * I) * cexp (-(2 * ↑real.pi * ↑a * I) * ↑x)) x), 
    {ext1 a,
    have : (λ (x : ℝ),cexp (-(2 * ↑real.pi * ↑a * ↑x * I))) = (λ (x : ℝ),cexp (-(2 * ↑real.pi * ↑a  * I) * ↑x)), by refine rewrite5,
    rw [this, deriv_exp_neg_complex_mul _ _],},
  simp_rw h₁,
  refine continuous.mul (continuous.neg _) _,
  refine continuous.mul _ continuous_const,
  refine continuous.mul continuous_const _,
  refine continuous.comp of_real_clm.continuous continuous_id,
  convert continuous_cexp,
  ext1 a,
  repeat {rw ← neg_mul,},
  rw [mul_assoc _ I _, mul_comm I _,← mul_assoc _ _ I],
end


lemma integrable_iterated_deriv_cexp_mul {f : schwartz_map ℝ ℂ} {n : ℕ} {x v : ℝ}: 
measure_theory.integrable (λ (v : ℝ), iterated_deriv n (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * f.to_fun v) x) measure_theory.measure_space.volume:=
begin
  simp_rw iterated_deriv_cexp_eq_mul_pow_cexp,
  convert integrable_exp_mul_schwartz2 x (const_pow_mul_schwartz_map n f),
  ext1 v,
  rw mul_assoc (cexp(_)) _ _,
  congr,
end


lemma deriv_cexp_mul_schwartz_moderate_decrease_const_pow_mul_schwartz 
{x : ℝ} {f : schwartz_map ℝ ℂ} {n : ℕ}:
∃ (C : ℝ), ∀ᵐ (a : ℝ), ∀ (y : ℝ), y ∈ metric.ball x (‖C‖ + 1) → ‖iterated_deriv (n + 1) (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑a * ↑w * I)) * f.to_fun a) y‖ ≤ C / (1 + ‖a‖ ^ 2) :=
begin
  have h := deriv_cexp_mul_schwartz_moderate_decrease (const_pow_mul_schwartz_map n f) x,
  obtain ⟨C,h⟩:=h,
  use C,
  convert h,
  ext1 a, ext1 y,
  split,
  repeat {intro h,
  intros w hw,
  specialize h w,
  specialize h hw,
  convert h,
  simp only [deriv_mul_const_field'],
  have h₄:deriv (λ (x : ℝ), cexp (-(2 * ↑real.pi * ↑a * ↑x * I))) w= deriv (λ (x : ℝ), cexp (-(2 * ↑real.pi *I *  ↑a)* ↑x)) w, by {congr,ext1,ring_nf,},
  rw [h₄, deriv_exp_neg_complex_mul _], 
  simp_rw iterated_deriv_cexp_eq_mul_pow_cexp,
  rw [pow_add,  mul_comm ((_)^n) _, mul_comm _ (cexp(_)), mul_assoc _ _ (f.to_fun _),
  mul_assoc _ _ ((const_pow_mul_schwartz_map n f).to_fun a), mul_assoc _ _ (f.to_fun _)],
  congr,
  repeat {rw ←neg_mul,},
  ring_nf,
  rw pow_one,},
end 


lemma iterated_deriv_eq_const_pow_mul_schwartz_map {f : schwartz_map ℝ ℂ} {n : ℕ} {a : ℝ} :
 (λ (x : ℝ), cexp (-(2 * ↑real.pi * ↑a * ↑x * I)) * (const_pow_mul_schwartz_map n f).to_fun a) = iterated_deriv n (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑a * ↑w * I)) * f.to_fun a) :=
begin
  have h := funext iterated_deriv_cexp_eq_mul_pow_cexp,
  simp at h,
  rw h,
  ext1 x,
  rw mul_assoc (cexp(_)) _ _,
  repeat {rw ← neg_mul,},
  congr,
end


lemma deriv_cexp_mul_const_pow_mul_schwartz_map {f : schwartz_map ℝ ℂ} {n : ℕ} {a w : ℝ}: 
deriv (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑a * ↑w * I)) * (const_pow_mul_schwartz_map n f).to_fun a) w = (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑a * ↑w * I)) * ((-2) * ↑real.pi * I * ↑a) ^ (n + 1) * f.to_fun a) w :=
begin
  simp only [deriv_mul_const_field'],
  have h₄:deriv (λ (x : ℝ), cexp (-(2 * ↑real.pi * ↑a * ↑x * I))) w= deriv (λ (x : ℝ), cexp (-(2 * ↑real.pi *I *  ↑a)* ↑x)) w, by {congr,ext1,ring_nf,},
  rw [h₄, deriv_exp_neg_complex_mul _,pow_add,pow_one], 
  dsimp only,
  rw mul_comm _ (cexp(_)),
  rw mul_assoc _ _ (f.to_fun _),
  rw mul_comm _ ((-2) * ↑real.pi * I * ↑a),
  rw ← mul_assoc, rw ← mul_assoc,
  rw mul_assoc _ _ (f.to_fun _),
  congr,
  repeat {rw ←neg_mul,},
  ring_nf,
end


lemma deriv_cexp_mul_const_pow_mul_schwartz_map_eq_iterated_deriv_succ {f : schwartz_map ℝ ℂ} {n : ℕ} {a w : ℝ} : 
deriv (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑a * ↑w * I)) * (const_pow_mul_schwartz_map n f).to_fun a) w = iterated_deriv (n + 1) (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑a * ↑w * I)) * f.to_fun a) w :=
begin
  rw iterated_deriv_cexp_eq_mul_pow_cexp,
  refine deriv_cexp_mul_const_pow_mul_schwartz_map,
end


lemma metric_ball_has_deriv_at_iterated_deriv {f : schwartz_map ℝ ℂ} {n : ℕ} {x C : ℝ} : 
∀ᵐ (a : ℝ), ∀ (x_1 : ℝ), x_1 ∈ metric.ball x (‖C‖ + 1) → has_deriv_at (λ (x : ℝ), iterated_deriv n (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑a * ↑w * I)) * f.to_fun a) x) (iterated_deriv (n + 1) (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑a * ↑w * I)) * f.to_fun a) x_1) x_1:=
begin
  have h :=metric_ball_has_deriv_at (const_pow_mul_schwartz_map n f),
  convert h,
  ext1 a, ext1 y,
  split,
  {intro h,
  intros w hw,
  specialize h w,
  specialize h hw,
  convert h,
  refine iterated_deriv_eq_const_pow_mul_schwartz_map,
  refine deriv_cexp_mul_const_pow_mul_schwartz_map_eq_iterated_deriv_succ,},
  {intro h,
  intros w hw,
  specialize h w,
  specialize h hw,
  convert h,
  ext1 x,
  rw ← iterated_deriv_eq_const_pow_mul_schwartz_map,
  symmetry,
  refine deriv_cexp_mul_const_pow_mul_schwartz_map_eq_iterated_deriv_succ,},
end


lemma has_deriv_at_iterated_deriv_fourier_transform  {x : ℝ} {f : schwartz_map ℝ ℂ} {n : ℕ}: 
has_deriv_at (iterated_deriv n (λ (w : ℝ), ∫ (v : ℝ), cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * f.to_fun v)) ((λ x : ℝ,(∫ (v : ℝ), iterated_deriv (n+1) (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * f.to_fun v) x)) x) x :=
begin
  have h₁:  ∀ᶠ (x : ℝ) in nhds x, measure_theory.ae_strongly_measurable ((λv : ℝ, iterated_deriv n (λw : ℝ,cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * f.to_fun v) x)) measure_theory.measure_space.volume,
    {simp_rw iterated_deriv_cexp_eq_mul_pow_cexp,--sorry,
    convert ae_strongly_measurable_cexp_mul_schwartz2 (const_pow_mul_schwartz_map n f),
    ext1 x, congr,ext1 v,rw mul_assoc _ _ (f.to_fun v), congr,},
  have h₂:  measure_theory.ae_strongly_measurable (λ (v : ℝ), iterated_deriv (n + 1) (λ (w : ℝ), cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * f.to_fun v) x) measure_theory.measure_space.volume, 
    {simp_rw iterated_deriv_cexp_eq_mul_pow_cexp,--sorry,
    convert ae_strongly_measurable_deriv_cexp_mul_schwartz2 (const_pow_mul_schwartz_map n f),
    ext1 w, rw deriv_cexp_mul_const_pow_mul_schwartz_map,},
  have h₄:= deriv_cexp_mul_schwartz_moderate_decrease_const_pow_mul_schwartz,
  obtain ⟨C,h₄⟩:=h₄,
  have h₃:= has_deriv_at_integral_of_dominated_loc_of_deriv_le _ h₁ (integrable_iterated_deriv_cexp_mul) h₂ _ _ _,
  dsimp at h₃,
  convert h₃.2,
  have h₅:= funext leibniz_rule_induction,
  simp at h₅,
  rw h₅,
  use (‖C‖+1),
  positivity,
  use 1,
  use (λ (x : ℝ), (C)/ (1 + ‖x‖ ^ 2)),
  convert h₄,
  refine integrable_moderate_decrease _,
  refine metric_ball_has_deriv_at_iterated_deriv,
end 


lemma differentiable_iterated_deriv_fourier_transform2 (f : schwartz_map ℝ ℂ) (n : ℕ) : 
differentiable ℝ (λ w : ℝ, iterated_deriv n (λ (w : ℝ), ∫ (v : ℝ), cexp (-(2 * ↑real.pi * ↑v * ↑w * I)) * f.to_fun v) w) :=
begin
  unfold differentiable,
  intro x,
  convert has_deriv_at.differentiable_at (has_deriv_at_iterated_deriv_fourier_transform),
end


def schwartz_fourier_transform (f :schwartz_map ℝ ℂ) : schwartz_map ℝ ℂ:=
{ to_fun := λ ξ  , real.fourier_integral f.to_fun ξ,
  smooth' :=
  begin
    simp,
    refine cont_diff_of_differentiable_iterated_deriv _,
    intros m hm,
    convert differentiable_iterated_deriv_fourier_transform2 f m,
    rw fourier_integral_eq_integral_exp_smul_funext,
  end,
  decay' :=
  begin
    exact fourier_transform_decay f,
  end,}


lemma continous_const_pow_mul_schwartz_map {h : ℝ} (g : schwartz_map ℝ ℂ) : 
measure_theory.ae_strongly_measurable (λ (x : ℝ), 𝓕 g.to_fun x * (λ (x : ℝ), cexp (-↑real.pi * ↑h * ↑‖x‖ ^ 2)) x) measure_theory.measure_space.volume:=
begin
  refine continuous.ae_strongly_measurable _,
  refine continuous.mul _ _,
  refine schwartz_map.continuous (schwartz_fourier_transform g),
  refine continuous.cexp  _,
  refine continuous.mul continuous_const _,
  norm_cast,
  refine continuous.comp of_real_clm.continuous _,
  refine continuous.pow _ 2,
  refine continuous_norm,
end


-- # From our previous file. Sorry'ed here :)
def gaussian_complex2  {a : ℂ} (ha : 0 < a.re) : schwartz_map ℝ ℂ :=
{ to_fun := λ x : ℝ , complex.exp (-a * ‖x‖^2),
  smooth' :=
  begin
    refine cont_diff.comp _ _,
    apply cont_diff.cexp,
    exact cont_diff_id,
    refine cont_diff.mul _ _,
    exact cont_diff_const,
    norm_cast,
    refine cont_diff.comp _ _,
    exact of_real_clm.cont_diff,
    exact cont_diff_norm_sq ℝ ,
  end,
  decay' := 
  begin
    sorry,
  end ,}


lemma moderate_decrease_mul_pre (f g : schwartz_map ℝ ℂ) :
∃ C : ℝ, ∀ x : ℝ, ‖f.to_fun x‖*‖g.to_fun x‖ ≤  (C)/ (1+‖x‖^2)^2:=
begin
  have h₁:=  moderate_decrease f,
  have h₂:= moderate_decrease g,
  obtain ⟨C₁,h₁⟩:=h₁,
  obtain ⟨C₂,h₂⟩:=h₂,
  use ((C₁*C₂)),
  intro x,
  rw [div_eq_mul_one_div, ← one_div_pow , pow_two, mul_assoc (C₁) (C₂) _, mul_comm C₂ _],
  repeat {rw ← mul_assoc,},
  rw mul_assoc _ (1 / (1 + ‖x‖ ^ 2)) C₂,
  refine mul_le_mul _ _ (norm_nonneg _) _,
  rw ← div_eq_mul_one_div,
  refine h₁ x,
  rw [mul_comm, ← div_eq_mul_one_div],
  refine h₂ x,
  rw ← div_eq_mul_one_div,
  refine le_trans _ (h₁ x),
  refine norm_nonneg _,
end


lemma one_div_le_one_div_pow_2 {x : ℝ}: 1/ (1+‖x‖^2)^2 ≤ 1/ (1+‖x‖^2) :=
begin
  rw one_div_le_one_div _ _,
  refine le_self_pow _ two_ne_zero,
  simp only [norm_eq_abs, pow_bit0_abs, le_add_iff_nonneg_right],
  positivity, positivity, positivity,
end


lemma moderate_decrease_mul (f g : schwartz_map ℝ ℂ) :
∃ C : ℝ, ∀ x : ℝ, ‖f.to_fun x‖*‖g.to_fun x‖ ≤  (C)/ (1+‖x‖^2) :=
begin
  have h := moderate_decrease_mul_pre f g,
  obtain ⟨C,h⟩:=h,
  use (C),
  intro x,
  specialize h x,
  have aux : ‖f.to_fun x‖*‖g.to_fun x‖* (1+‖x‖^2)^2 ≤  (C),
    rw ← le_div_iff _, refine h, positivity,
  refine le_trans h _,
  rw [div_eq_mul_one_div],
  nth_rewrite 1 div_eq_mul_one_div,
  refine mul_le_mul rfl.ge one_div_le_one_div_pow_2 _ _,
  positivity,
  refine le_trans _ aux,
  positivity,
end


lemma tendsto_integral_one_div_one_add_sq_real_pi:  
tendsto (λn : ℝ, ∫ (x : ℝ) in -n..n, (λ (x : ℝ), 1 / (1 + x ^ 2)) x) at_top (nhds (real.pi / 2 + real.pi / 2)) :=
begin
  simp_rw integral_one_div_one_add_sq,
  simp_rw sub_eq_add_neg,
  refine filter.tendsto.add tendsto_arctan_at_top _,
  simp_rw [real.arctan_neg _,neg_neg],
  refine tendsto_arctan_at_top,
end


lemma exist_integral_moderate_decrease_bounded (C : ℝ) : 
∃ I: ℝ , ∫ (x : ℝ), (λ (x : ℝ), ‖C‖ / (1 + ‖x‖ ^ 2)) x ≤ I:=
begin
  use (((real.pi/2)+(real.pi/2))*‖C‖),
  have h₁: ∫ (x : ℝ), (λ (x : ℝ), ‖C‖ / (1 + ‖x‖ ^ 2)) x = (∫ (x : ℝ), 1 / (1 + ‖x‖ ^ 2)) * ‖C‖, 
  {rw [←smul_eq_mul,←integral_smul_const], congr, ext1, dsimp only,
   rw [div_eq_mul_one_div,smul_eq_mul, mul_comm],},
  rw h₁,
  refine mul_le_mul _ rfl.ge (norm_nonneg _) _,
  have h₂: tendsto (λn : ℝ, ∫ (x : ℝ) in -n..n, (λ (x : ℝ), 1 / (1 + ‖x‖ ^ 2)) x) at_top (nhds (real.pi / 2 + real.pi / 2)), 
    {convert tendsto_integral_one_div_one_add_sq_real_pi, ext1 n,
    congr, dsimp only, ext1 x,simp only [norm_eq_abs, pow_bit0_abs],},
  refine  tendsto_nhds_unique_le _ h₂,
  have h₃:= n_top_integral_real (λ x : ℝ,(λ (x : ℝ), 1 / (1 + ‖x‖ ^ 2)) x) (integrable_moderate_decrease _),
  dsimp only at h₃,
  convert h₃,
  rw ←zero_add (0: ℝ), 
  refine add_le_add (le_of_lt real.pi_div_two_pos) (le_of_lt real.pi_div_two_pos),
end


-- # From our previous file. Sorry'ed here :)
lemma exp_a_neg_sq_le_one {a : ℂ} (ha : 0 < a.re) : 
∀ x : ℝ , complex.abs (complex.exp (-a*x^2)) ≤ 1 := sorry


lemma schwartz_mul_cexp_moderate_decrease_nhds_within_0 (g : schwartz_map ℝ ℂ) : 
∃ C : ℝ, ∀ᶠ (n : ℝ) in nhds_within 0 (Ioi 0), ∀ᵐ (a : ℝ), ‖𝓕 g.to_fun a * (λ (x : ℝ), cexp (-↑real.pi * ↑n * ↑‖x‖ ^ 2)) a‖ ≤ ‖C‖  / (1 + ‖a‖ ^ 2) :=
begin
  have h₈:= moderate_decrease (schwartz_fourier_transform g),
  obtain ⟨C,h₈⟩:=h₈,
  use C,
  refine eventually_nhds_within_iff.mpr _,
  refine eventually_of_forall _,
  intros n hn,
  have hπn : 0< ((real.pi*n) : ℂ).re, by by {norm_cast, rw set.mem_Ioi at hn, rw zero_lt_mul_right hn, exact pi_pos,},
  have h₂:=moderate_decrease ((gaussian_complex2 hπn)),
  obtain ⟨C₂,h₂⟩:=h₂,
  refine eventually_of_forall _,
  intro x,
  rw [norm_mul,  ← mul_one (‖C‖ / (1 + ‖x‖ ^ 2))], 
  refine mul_le_mul _ _ (norm_nonneg _) _,
  {convert le_trans (h₈ x) (le_norm_self _),
  rw norm_div, 
  congr,
  simp only [norm_eq_abs, pow_bit0_abs],
  symmetry,
  rw abs_eq_self,
  positivity,},
  {have hπn : 0< ((real.pi*n) : ℂ).re, by by {norm_cast, rw zero_lt_mul_right hn, exact pi_pos,},
  convert exp_a_neg_sq_le_one hπn x, 
  have h₁: (x : ℂ) ^ 2 = ‖x‖ ^ 2, norm_cast,simp only [norm_eq_abs, pow_bit0_abs],
  rw h₁,
  repeat {rw ←neg_mul,},},
  {positivity,},
end


lemma tendsto_coe:  tendsto (λ (k : ℝ), (k : ℂ)) (nhds_within 0 (Ioi 0)) (nhds 0) :=
begin
  exact (complex.continuous_of_real.tendsto' 0 _ complex.of_real_zero).mono_left nhds_within_le_nhds,
end


lemma converges_proper (g : schwartz_map ℝ ℂ) : 
tendsto (λ δ : ℝ  ,  ∫ (x : ℝ), 𝓕 g.to_fun x * ((λ x : ℝ , complex.exp (-real.pi *δ* ‖x‖^2)) x)) (nhds_within 0 (set.Ioi 0)) (nhds (∫ (x : ℝ), 𝓕 g.to_fun x)) :=
begin
  have h₂: ∃ C : ℝ, ∀ᶠ (n : ℝ) in nhds_within 0 (Ioi 0), ∀ᵐ (a : ℝ), ‖𝓕 g.to_fun a * (λ (x : ℝ), cexp (-↑real.pi * ↑n * ↑‖x‖ ^ 2)) a‖ ≤ ‖C‖  / (1 + ‖a‖ ^ 2), 
    refine schwartz_mul_cexp_moderate_decrease_nhds_within_0 g,
  obtain ⟨C,h₂⟩:=h₂,
  refine  measure_theory.tendsto_integral_filter_of_dominated_convergence _ _ h₂ _ _,
  {refine filter.eventually_of_forall _, intro x, exact continous_const_pow_mul_schwartz_map _,},
  convert integrable_moderate_decrease _,
  refine filter.eventually_of_forall _,
  intro x,
  have  h₁: 𝓕 g.to_fun x = 𝓕 g.to_fun x * 1, rw mul_one,
  nth_rewrite 0 h₁,
  refine filter.tendsto.mul _ _,
  simp only [tendsto_const_nhds_iff],
  have h₂: cexp(0) = 1, simp only [complex.exp_zero],
  rw ← h₂,
  refine filter.tendsto.cexp _,
  have h₃: 0 = 0 * ((‖x‖: ℂ) ^ 2), rw zero_mul,
  rw h₃,
  refine filter.tendsto.mul_const _ _,
  have h₄: 0 =  (-real.pi: ℂ) * 0, rw mul_zero,
  rw h₄,
  refine filter.tendsto.const_mul _ _,
  refine tendsto_coe,
end


def schwartz_mul  (f : schwartz_map ℝ ℂ) (h : ℝ) : schwartz_map ℝ ℂ :=
{ to_fun := λ (y : ℝ), f.to_fun (h*y),
  smooth' :=
  begin
    refine cont_diff.comp f.smooth' _,
    refine cont_diff.mul (cont_diff_const) (cont_diff_id),
  end,
  decay' := 
  begin
    sorry, -- realized we needed this, have not have had the time to formalize
  end ,}


lemma cexp_delta_cancel {δ x : ℝ} {f : schwartz_map ℝ ℂ} (h : 0 < δ) : (λ (v : ℝ), cexp (↑((-2) * real.pi * 1 / δ * (δ * v) * x) * I) • f.to_fun (δ * v)) = λ (v : ℝ), cexp (-(2 * ↑real.pi * ↑v * ↑x * I)) * (schwartz_mul f δ).to_fun v :=
begin
  ext1 v,  congr,
  repeat {rw ←neg_mul,},
  norm_cast,
  repeat {rw ← mul_assoc,},
  rw [mul_assoc _ v x, mul_assoc _ v x,mul_comm _ (v*x),mul_comm _ (v*x),
  mul_div_assoc,mul_assoc _ (1/δ) δ,one_div_mul_cancel, mul_one],
  positivity,
end


lemma tendsto1 {δ x : ℝ} {f : schwartz_map ℝ ℂ} (h : 0 < δ) : tendsto (λn : ℝ,∫ (v : ℝ) in -n..n, (λw : ℝ,  cexp (↑((-2) * real.pi * 1/δ*(w) * x) * I) • f.to_fun (w)) (δ*v)) at_top (nhds(∫ (v : ℝ), (λw : ℝ,  cexp (↑((-2) * real.pi * 1/δ*(w) * x) * I) • f.to_fun (w)) (δ*v))) :=
begin 
  simp_rw rewrite_imaginary_part,
  have h₁: tendsto (λ (n : ℝ), -n) at_top at_bot, by {simp only [tendsto_neg_at_bot_iff], exact rfl.ge,},
  have h₂: tendsto (λ (n : ℝ), n) at_top at_top, by {exact rfl.ge,},
  convert measure_theory.interval_integral_tendsto_integral (integrable_exp_mul_schwartz2 (x) (schwartz_mul f δ)) h₁ h₂,
  {ext1 n,  congr,refine cexp_delta_cancel h,},
  {refine cexp_delta_cancel h,},
end


lemma cexp_bound' (h : ℝ) {a : ℝ} : 
∃ (C : ℝ), ∀ (x : ℝ), ‖cexp (↑((a) * x * h) * I)‖ ≤ C :=
begin
  use 1,  intro x,  rw [complex.norm_exp_of_real_mul_I _],
end


lemma continuous_cexp' {x a : ℝ} : continuous (λ (v : ℝ), cexp ((a : ℂ) * ↑v * ↑x * I)) :=
begin
  refine continuous.cexp  _,
  refine continuous.mul _ continuous_const,
  refine continuous.mul _ continuous_const,
  refine continuous.mul continuous_const _,
  refine continuous.comp of_real_clm.continuous continuous_id,
end


lemma integrable_exp_mul_schwartz4 (x : ℝ) (f : schwartz_map ℝ ℂ){C : ℝ}:
measure_theory.integrable (λ (v : ℝ), (λ (w : ℝ), cexp (((C) * ↑v * ↑w * I)) * f.to_fun v) x) measure_theory.measure_space.volume:=
begin
  convert integrable_mul_schwartz_map _ (λ (v : ℝ), cexp ((C * ↑v * ↑x * I))) (integrable_schwartz_map (f)) _ _,
  have h₂:=cexp_bound' x,
  obtain ⟨C,h₂⟩:=h₂,
  use C,
  intro x, specialize h₂ x,
  convert h₂,
  repeat {rw ←neg_mul,},
  norm_cast,
  convert continuous_cexp',
end


lemma cexp_const_mul_smul {δ x : ℝ} {f : schwartz_map ℝ ℂ}: 
(λ (v : ℝ), cexp (-(2 * ↑real.pi * ↑(x / δ) * ↑v * I)) • f.to_fun v) = λ (v : ℝ), cexp (↑(((-2:ℤ) : ℝ) * real.pi * (1 / δ)) * ↑v * ↑x * I) * f.to_fun v :=
begin
  ext1 v,
  rw smul_eq_mul,
  repeat {rw ← neg_mul,},
  rw div_eq_mul_one_div,
  nth_rewrite_rhs 0 mul_assoc, 
  nth_rewrite_rhs 0 mul_assoc, 
  rw [← mul_assoc (v : ℂ) (x : ℂ) _, mul_comm (v : ℂ) (x : ℂ)],
  repeat {rw ← mul_assoc,},
  rw mul_comm x _,
  norm_cast,
  repeat {rw ← mul_assoc,},
end


lemma tendsto2{δ x : ℝ} {f : schwartz_map ℝ ℂ} (h : 0 < δ) : 
tendsto (λ (n : ℝ), (1 / (δ: ℂ)) * ∫ (v : ℝ) in (δ * -n)..(δ * n), (λ (w : ℝ), cexp (↑((-(2: ℝ)) * real.pi * 1 / δ * w * x) * I) • f.to_fun w) (v)) at_top (nhds (1 / ↑δ * ∫ (v : ℝ), cexp (↑((-(2: ℝ)) * real.pi * v * (x / δ)) * I) • f.to_fun v)) :=
begin
  simp_rw rewrite_imaginary_part,
  refine filter.tendsto.const_mul _ _,
  have h₁: tendsto (λ (n : ℝ), δ*(-n)) at_top at_bot, by {simp only [mul_neg,tendsto_neg_at_bot_iff],refine filter.tendsto.const_mul_at_top h _, exact rfl.ge,},
  have h₂: tendsto (λ (n : ℝ), δ*(n)) at_top at_top, by {refine filter.tendsto.const_mul_at_top h _, exact rfl.ge,},
  have h₃: 0<1/δ, positivity,
  have h₄:= measure_theory.interval_integral_tendsto_integral (integrable_exp_mul_schwartz4 (x) f) h₁ h₂,
  dsimp at h₄,
  convert h₄,
  {ext1 n, congr, ext1 v,
  rw ← smul_eq_mul,
  repeat {rw ← neg_mul,},
  congr,
  rw mul_div_assoc,
  norm_cast,},
  {refine cexp_const_mul_smul,},
end


lemma proposition_1_2_iii {x δ : ℝ} (f : schwartz_map ℝ ℂ) (h : 0 < δ) : 
real.fourier_integral (λ (y : ℝ), f.to_fun (δ*y)) x = (1/δ) * real.fourier_integral f.to_fun (x/δ) :=
begin
  rw fourier_integral_eq_integral_exp_smul,
  rw fourier_integral_eq_integral_exp_smul,
  have h₁: ∫ (v : ℝ), cexp (↑((-2) * real.pi * v * x) * I) • f.to_fun (δ * v) = ∫ (v : ℝ), (λw : ℝ,  cexp (↑((-2) * real.pi * 1/δ*(w) * x) * I) • f.to_fun (w)) (δ*v), 
    congr, ext1 v, dsimp only, rw mul_div_assoc,rw mul_assoc _ (1 / δ) _, congr, ring_nf, rw [mul_assoc, ←one_div, mul_comm δ _,one_div_mul_cancel,mul_one],positivity,
  rw h₁,
  refine tendsto_nhds_unique (tendsto1 h) _,
  convert tendsto2 h,
  ext1 n,
  rw interval_integral.integral_comp_mul_left,
  rw ← smul_eq_mul,
  rw one_div,
  norm_cast,
  positivity,
end


lemma cexp_sqrt_delta_eq_cexp_abs {x δ : ℝ} (h : 0 < δ) : 
cexp (-(real.pi: ℂ) * ↑(x / δ ^ ((1 / 2) : ℝ)) ^ 2) = cexp (-(↑real.pi / ↑δ) * ↑|x| ^ 2) :=
begin
  norm_cast,
  rw div_pow,
  rw div_eq_mul_one_div,
  nth_rewrite_rhs 0 div_eq_mul_one_div,
  rw ← neg_mul,
  repeat {rw ← mul_assoc,},
  have h₁: (δ ^ ((1 / 2) : ℝ)) ^ 2 = δ, by {rw [← real.sqrt_eq_rpow, real.sq_sqrt], positivity,},
  rw [h₁, mul_assoc _ (x^2) _, mul_comm (x^2) _, ← mul_assoc _ _ (x^2), ← abs_sq],
  congr,
  simp only [_root_.abs_pow],
end


lemma fourier_integral_norm_sqrt_delta {x δ : ℝ} (h : 0 < δ) : 
real.fourier_integral  (λ x : ℝ, complex.exp (-((real.pi*δ) : ℂ)* ‖x‖^2)) x = real.fourier_integral  (λ x : ℝ, (λ y : ℝ,complex.exp (-((real.pi) : ℂ)* ‖y‖^2)) ((δ^((1/2) : ℝ))*x)) x :=
begin
  congr,
  dsimp,
  norm_cast,
  ext1 x,
  rw [abs_mul, mul_pow, ←neg_mul],
  repeat {rw ← mul_assoc,},
  congr, 
  simp only [_root_.abs_pow],
  rw [← real.sqrt_eq_rpow, ← norm_eq_abs, ← norm_pow, real.sq_sqrt, norm_eq_abs],
  symmetry,
  rw abs_eq_self,
  positivity,
  positivity,
end


lemma gaussian_pi_eq_gaussian_complex_pi {x δ : ℝ} (h : 0 < δ) : 
𝓕 gaussian_pi.to_fun (x / δ ^ ((1 / 2) : ℝ)) = 𝓕 gaussian_complex_pi.to_fun (x / δ ^ ((1 / 2) : ℝ)) :=
begin
  rw fourier_integral_eq_integral_exp_smul,
  rw fourier_integral_eq_integral_exp_smul,
  congr,
  ext1 v,
  have h₁: gaussian_complex_pi.to_fun = λ x : ℝ, complex.exp (-real.pi * x ^ 2), refl,
  have h₂: gaussian_pi.to_fun = λ x : ℝ, complex.exp (-real.pi * ‖x‖ ^ 2), refl,
  rw [h₁,h₂],
  dsimp,
  norm_cast,
  have : (v) ^ 2 = |v| ^ 2, simp only [pow_bit0_abs],
  rw this,
end


lemma good_kernel_fourier_transform(x : ℝ) {δ : ℝ} (hδ : 0<δ) : 
real.fourier_integral  (λ x : ℝ, complex.exp (-((real.pi*δ) : ℂ)* ‖x‖^2)) x  = (λ x : ℝ, (sqrt (1 / δ) : ℂ)  * complex.exp ((-((real.pi/δ) : ℂ)* ‖x‖^2))) x :=
begin
  have h₁: 0< ((real.pi*δ) : ℂ).re, by {norm_cast,rw zero_lt_mul_right hδ,exact pi_pos,},
  have h₃: real.fourier_integral  (λ x : ℝ, complex.exp (-((real.pi*δ) : ℂ)* ‖x‖^2)) x = real.fourier_integral  (λ x : ℝ, (λ y : ℝ,complex.exp (-((real.pi) : ℂ)* ‖y‖^2)) ((δ^((1/2) : ℝ))*x)) x, by {refine fourier_integral_norm_sqrt_delta hδ,},
  have h₄: 𝓕 (λ (x : ℝ), (λ (y : ℝ), cexp (-↑real.pi * ↑‖y‖ ^ 2)) (δ ^ ((1 / 2) : ℝ) * x)) x = 𝓕 (λ (x : ℝ), (gaussian_pi.to_fun) (δ ^ ((1 / 2) : ℝ) * x)) x, by {congr,},
  have h₅:= proposition_1_2_iii (gaussian_pi) _,
  rw [h₃,h₄,h₅],
  congr,
  norm_cast,
  rw [← real.sqrt_eq_rpow, sqrt_div, sqrt_one],
  refine zero_le_one,
  have h₆:= fourier_transform_eq_gaussian2 (x / δ ^ ((1 / 2) : ℝ)),
  have h₇: gaussian_complex_pi.to_fun = λ x : ℝ, complex.exp (-real.pi * x ^ 2), refl,
  rw [gaussian_pi_eq_gaussian_complex_pi hδ,h₆,h₇],
  dsimp, rw cexp_sqrt_delta_eq_cexp_abs hδ, positivity,
end


theorem complex_coe_ne_zero {δ : ℝ} (hδ : 0<δ) : (δ: ℂ) ≠ 0:=
begin
  norm_cast,
  exact ne_of_gt hδ,
end


theorem integral_good_kernel_eq_one {δ : ℝ} (hδ : 0<δ) : 
∫ x : ℝ,  (1 / (δ: ℂ)^ ((1 /2) :ℤ))*cexp (- (real.pi/δ)* x^2) = 1 :=
begin
  have hπδ : 0< ((real.pi/δ) : ℂ).re, by {norm_cast, rw [lt_div_iff hδ, zero_mul], exact pi_pos,},
  have h :=integral_gaussian_complex hπδ,
  simp_rw [mul_comm (1 / (δ: ℂ)^ (_ / _)) _, ← smul_eq_mul],
  rw integral_smul_const,
  simp_rw smul_eq_mul,
  rw [h,div_div_eq_mul_div , mul_div_right_comm, div_self _, one_mul,←div_eq_mul_one_div], 
  refine div_self (zpow_ne_zero _ _),
  refine complex_coe_ne_zero hδ,
  refine complex_coe_ne_zero pi_pos,
end

-- sorry for now
lemma iterated_fderiv_add {f : schwartz_map ℝ ℝ} {x h : ℝ} {n : ℕ}: 
iterated_fderiv ℝ n f.to_fun (h + x) =  iterated_fderiv ℝ n (λ (y : ℝ), f.to_fun (h + y)) x :=
begin
  sorry,
end

lemma norm_iterated_fderiv_add {f : schwartz_map ℝ ℂ} {x h : ℝ} {n : ℕ}: 
‖iterated_fderiv ℝ n f.to_fun (h + x)‖ =  ‖iterated_fderiv ℝ n (λ (y : ℝ), f.to_fun (h + y)) x‖:=
begin
  rw iterated_fderiv_add,
end

lemma iterated_fderiv_sub {f : schwartz_map ℝ ℂ} {x h : ℝ} {n : ℕ}: 
‖iterated_fderiv ℝ n f.to_fun (h - x)‖ =  ‖iterated_fderiv ℝ n (λ (y : ℝ), f.to_fun (h - y)) x‖:=
begin
  sorry,
end


lemma schwartz_add_bound_sum {f : schwartz_map ℝ ℂ} {x h : ℝ} {n k : ℕ}: 
‖x‖ ^ k * ‖iterated_fderiv ℝ n f.to_fun (h + x)‖ ≤ (‖x + h‖ + ‖h‖)^k * ‖iterated_fderiv ℝ n f.to_fun (h + x)‖:=
begin
  have h₆: ‖x‖^k ≤ (‖x + h‖ + ‖h‖)^k, by refine pow_le_pow_of_le_left (norm_nonneg _) (norm_le_add_norm_add x h) k,
  refine mul_le_mul h₆ rfl.ge (norm_nonneg _) _,    positivity,
end


lemma schwartz_sub_bound_sum {f : schwartz_map ℝ ℂ} {x h : ℝ} {n k : ℕ}: 
‖x‖ ^ k * ‖iterated_fderiv ℝ n f.to_fun (h - x)‖ ≤ (‖x - h‖ + ‖h‖)^k * ‖iterated_fderiv ℝ n f.to_fun (h - x)‖:=
begin
  have h₆: ‖x‖^k ≤ (‖x - h‖ + ‖h‖)^k,
  {refine pow_le_pow_of_le_left (norm_nonneg _) _ k,
  rw add_comm,  refine norm_le_insert' _ _,},
  {refine mul_le_mul h₆ rfl.ge (norm_nonneg _) _,
  positivity,},
end


lemma schwartz_sum_decay (f : schwartz_map ℝ ℂ) :
∀ (k n : ℕ), ∃ (C : ℝ), ∀ (x : ℝ), ∑ (m : ℕ) in range (k + 1), ‖x‖ ^ m * ‖iterated_fderiv ℝ n f.to_fun x‖ ≤ C :=
begin
  intro k,
  induction k with k hk,
  have h :=f.decay',
  intro n,
  specialize h 0,
  specialize h n,
  obtain ⟨C,h⟩:=h,
  use C,
  intro x,
  simp only [range_one, sum_singleton, pow_zero, one_mul],
  specialize h x,
  rw [pow_zero, one_mul] at h,
  refine h,
  intro n,
  have h :=f.decay',
  specialize h (k+1), 
  specialize h n,
  specialize hk n,
  obtain ⟨C₁,hk⟩:=hk,
  obtain ⟨C₂,h⟩:=h,
  use (C₁+C₂),
  intro x,
  rw finset.sum_range_succ,
  specialize h x,
  specialize hk x,
  refine add_le_add hk h,
end


lemma zero_le_sum_norm_mul_norm {f : schwartz_map ℝ ℂ} {a b : ℝ} {k n : ℕ}: 
0 ≤ ∑ (m : ℕ) in range (k + 1), ‖a‖ ^ m * ‖iterated_fderiv ℝ n f.to_fun (b)‖:=
begin 
  induction k with k hk,
  simp only [range_one, sum_singleton, pow_zero, one_mul, norm_nonneg],
  rw finset.sum_range_succ,
  positivity,
end


lemma sum_le_sum {f g : ℕ → ℝ} {k : ℕ} (h : ∀ i: ℕ, i≤ k →  f i ≤ g i) : 
∑ (m : ℕ) in range (k + 1), f m ≤ ∑ (m : ℕ) in range (k + 1), g m :=
begin
  induction k with k hk,
  simp only [range_one, sum_singleton],
  refine h 0 rfl.ge,
  rw finset.sum_range_succ,
  nth_rewrite 1 finset.sum_range_succ,
  refine add_le_add _ _,
  specialize hk _,
  intro i,
  specialize h i,
  intro hi,
  refine h _,
  refine le_trans hi _,
  rw nat.succ_eq_add_one,
  simp only [le_add_iff_nonneg_right, zero_le'],
  refine hk,
  specialize h (k+1),
  refine h _,
  rw nat.succ_eq_add_one,
end


lemma sum_pow_mul_schwartz_le_const_mul_sum_schwartz {f : schwartz_map ℝ ℂ} {k n : ℕ} {x h : ℝ}: 
∑ (m : ℕ) in range (k + 1), ‖x + h‖ ^ m * ‖h‖ ^ (k - m) * ↑(k.choose m) * ‖iterated_fderiv ℝ n f.to_fun (h + x)‖ ≤ ∑ (m : ℕ) in range (k + 1),  (2^k * (1+‖h‖) ^ (k)) * ‖x + h‖ ^ m  * ‖iterated_fderiv ℝ n f.to_fun (h + x)‖:=
begin
  rw [← sum_mul,←sum_mul],
  refine mul_le_mul _ rfl.ge (norm_nonneg _) _,
  {simp_rw [mul_comm _ (‖x + h‖ ^ _), mul_comm _ ((1 + ‖h‖)^_), ← mul_assoc],
  refine sum_le_sum _,
  intros i hi,
  refine mul_le_mul _ _ _ _,
  {refine mul_le_mul rfl.ge _ _ _,
  {have h₁: ‖h‖ ^ (k-i) ≤ (1 + ‖h‖) ^ (k-i), by {refine pow_le_pow_of_le_left (norm_nonneg _) _ _, simp only [le_add_iff_nonneg_left, zero_le_one],},
  refine le_trans h₁ _,
  refine pow_le_pow _ _,
  {simp only [norm_eq_abs, le_add_iff_nonneg_right, abs_nonneg],},
  {simp only [tsub_le_self],},},  positivity,  positivity,},
  {have h₂: (2: ℝ)^k = (2: ℕ)^k, norm_cast,
  rw [h₂],
  norm_cast,
  rw [← nat.sum_range_choose k],
  refine finset.single_le_sum _ _,
  intros i hi,
  positivity,
  simp only [finset.mem_range], linarith,}, {positivity,}, {positivity,},},
  {apply finset.sum_nonneg,  intros i hi,  positivity,},
end


lemma sum_pow_mul_schwartz_le_const_mul_sum_schwartz_sub {f : schwartz_map ℝ ℂ} {x h : ℝ} {k n : ℕ}: 
∑ (m : ℕ) in range (k + 1), ‖x - h‖ ^ m * ‖h‖ ^ (k - m) * ↑(k.choose m) * ‖iterated_fderiv ℝ n f.to_fun (h - x)‖ ≤ ∑ (m : ℕ) in range (k + 1),  (2^k * (1+‖h‖) ^ (k)) * ‖x - h‖ ^ m  * ‖iterated_fderiv ℝ n f.to_fun (h - x)‖:=
begin
  rw [← sum_mul,←sum_mul],
  refine mul_le_mul _ rfl.ge (norm_nonneg _) _,
  {simp_rw [mul_comm _ (‖x - h‖ ^ _), mul_comm _ ((1 + ‖h‖)^_), ← mul_assoc],
  refine sum_le_sum _,
  intros i hi,
  refine mul_le_mul _ _ _ _,
  {refine mul_le_mul rfl.ge _ _ _,
  {have h₁: ‖h‖ ^ (k-i) ≤ (1 + ‖h‖) ^ (k-i), by {refine pow_le_pow_of_le_left (norm_nonneg _) _ _, simp only [le_add_iff_nonneg_left, zero_le_one],},
  refine le_trans h₁ _,
  refine pow_le_pow _ _,
  {simp only [norm_eq_abs, le_add_iff_nonneg_right, abs_nonneg],},
  {simp only [tsub_le_self],},},  positivity,  positivity,},
  {have h₂: (2: ℝ)^k = (2: ℕ)^k, norm_cast,
  rw [h₂],
  norm_cast,
  rw [← nat.sum_range_choose k],
  refine finset.single_le_sum _ _,
  intros i hi,
  positivity,
  simp only [finset.mem_range], linarith,}, {positivity,}, {positivity,},},
  {apply finset.sum_nonneg,  intros i hi,  positivity,},
end


def schwartz_add  (f : schwartz_map ℝ ℂ) (h : ℝ) : schwartz_map ℝ ℂ :=
{ to_fun := λ (y : ℝ), f.to_fun (h + y),
  smooth' :=
  begin
    refine cont_diff.comp f.smooth' _,
    refine cont_diff.add (cont_diff_const) (cont_diff_id),
  end,
  decay' := 
  begin
    have h₁:= schwartz_sum_decay f,
    intros k n,
    specialize h₁ k, 
    specialize h₁ n, 
    obtain ⟨C,h₁⟩:=h₁,
    use (2 ^ k * (1 + ‖h‖) ^ k*C),
    intro x,
    specialize h₁ (h +x), 
    rw ← norm_iterated_fderiv_add,
    refine le_trans schwartz_add_bound_sum _,
    rw [add_pow, finset.sum_mul],
    refine le_trans sum_pow_mul_schwartz_le_const_mul_sum_schwartz _,
    simp_rw mul_assoc _ (‖x + h‖ ^ _) _,
    rw ← finset.mul_sum,
    simp_rw add_comm,
    refine mul_le_mul rfl.ge h₁ _ _,
    refine zero_le_sum_norm_mul_norm,
    positivity,
  end ,}


def schwartz_sub (f : schwartz_map ℝ ℂ) (h : ℝ) : schwartz_map ℝ ℂ :=
{ to_fun := λ (y : ℝ), f.to_fun (h - y),
  smooth' :=
  begin
    refine cont_diff.comp f.smooth' _,
    refine cont_diff.sub (cont_diff_const) (cont_diff_id),
  end,
  decay' := 
  begin
    have h₁:= schwartz_sum_decay f,
    intros k n,
    specialize h₁ k, 
    specialize h₁ n, 
    obtain ⟨C,h₁⟩:=h₁,
    use (2 ^ k * (1 + ‖h‖) ^ k*C),
    intro x,
    specialize h₁ (h-x), 
    rw ← iterated_fderiv_sub,
    refine le_trans schwartz_sub_bound_sum _,
    rw [add_pow, finset.sum_mul],
    refine le_trans sum_pow_mul_schwartz_le_const_mul_sum_schwartz_sub  _,
    simp_rw mul_assoc _ (‖x - h‖ ^ _) _,
    rw ← finset.mul_sum,
    refine mul_le_mul rfl.ge _ _ _,
    convert h₁,
    ext1 m,
    rw [sub_eq_add_neg,← norm_neg,add_comm],
    congr, ring_nf,
    refine zero_le_sum_norm_mul_norm,
    positivity,
  end ,}


lemma integrable_fun1 (g : schwartz_map ℝ ℂ) {x δ : ℝ} (hδ : 0 < δ) : 
measure_theory.integrable (λ (a : ℝ), g.to_fun (x - a) * (1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖a‖ ^ 2))) measure_theory.measure_space.volume:=
begin
  have h := (schwartz_sub g x).decay',
  specialize h 0,
  specialize h 0,
  obtain ⟨C,h⟩:=h,
  refine  measure_theory.integrable.bdd_mul' _ _ _,
  exact C,
  have h₁: ∀ a : ℝ, cexp (-(↑real.pi / ↑δ) * ↑‖a‖ ^ 2) = (λ y : ℝ, cexp (-(↑real.pi / ↑δ) * ↑‖y‖ ^ 2)) a, by {intro a, simp,},
  simp_rw h₁ _,
  refine  measure_theory.integrable.const_mul _ (1 / ↑δ ^ (1 / 2)),
  have hδcomplex : 0 < (real.pi/δ: ℂ).re, by {norm_cast, rw [lt_div_iff hδ, zero_mul], exact pi_pos,},
  convert integrable_schwartz_map (gaussian_complex hδcomplex),
  refine continuous.ae_strongly_measurable _,
  have h₂:=schwartz_map.continuous (schwartz_sub g x),
  refine h₂,
  refine filter.eventually_of_forall _,
  simp only [pow_zero, norm_iterated_fderiv_zero, one_mul] at h,
  have h₁: (schwartz_sub g x).to_fun =  λ (y : ℝ), g.to_fun (x - y), by refl,
  rw h₁ at h,
  refine h,
end


lemma integrable_fun2 (g : schwartz_map ℝ ℂ) {x δ : ℝ} (hδ : 0 < δ) : 
measure_theory.integrable (λ (a : ℝ), (1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑a ^ 2)) • g.to_fun x) measure_theory.measure_space.volume:=
begin
  simp_rw smul_eq_mul,
  simp_rw mul_comm _ (g.to_fun _),
  refine measure_theory.integrable.bdd_mul _ _ _,
  refine  measure_theory.integrable.const_mul _ _,
  have hδcomplex : 0 < (real.pi/δ: ℂ).re, by {norm_cast, rw [lt_div_iff hδ, zero_mul], exact pi_pos,},
  convert integrable_schwartz_map (gaussian_complex hδcomplex),
  have h₁: (gaussian_complex hδcomplex).to_fun = λ x : ℝ , complex.exp (-(real.pi/δ)* ‖x‖^2), by refl,
  {rw h₁, ext1 x, have : (x : ℂ) ^ 2 = ‖x‖ ^ 2, norm_cast,simp only [norm_eq_abs, pow_bit0_abs],  rw ← this,},
  refine continuous.ae_strongly_measurable _,
  refine continuous_const,
  use ‖g.to_fun x‖,
  intro y, exact rfl.ge,
end

-- Credit to Eric Weiser
lemma Icc_disjoint_Iio {μ : ℝ} (h : 0≤ μ) : disjoint (Icc (-μ) μ) (Ioi μ) :=
(set.Iic_disjoint_Ioi le_rfl).mono_left set.Icc_subset_Iic_self


lemma integrable_good_kernel_expression (g : schwartz_map ℝ ℂ) {x δ : ℝ} (hδ : 0< δ) :
 measure_theory.integrable (λ (y : ℝ), 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖y‖ ^ 2) * (g.to_fun (x -y) - g.to_fun x)) measure_theory.measure_space.volume:=
begin
  have hπδ : 0< ((real.pi/δ) : ℂ).re, by {norm_cast, rw [lt_div_iff hδ, zero_mul], exact pi_pos,},
  have h₁: (λ (y : ℝ), 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖y‖ ^ 2) * (g.to_fun (x -y) - g.to_fun x)) = (λ (y : ℝ), 1 / ↑δ ^ (1 / 2) * (λ y : ℝ, cexp (-(↑real.pi / ↑δ) * ↑‖y‖ ^ 2) * (g.to_fun (x -y) - g.to_fun x)) y),
    ext1, dsimp, rw mul_assoc,
  rw h₁,
  refine measure_theory.integrable.const_mul _ _,
  dsimp only,
  simp_rw mul_sub,
  refine measure_theory.integrable.sub _ _,
  {refine integrable_mul_schwartz_map (schwartz_sub g x) _ (integrable_schwartz_map _) _ _,
  {have h₁:= (gaussian_complex2 hπδ).decay',
  specialize h₁ 0, specialize h₁ 0, 
  simp only [pow_zero, norm_iterated_fderiv_zero, one_mul] at h₁,
  convert h₁,},
  {refine continuous.cexp  _,
  refine continuous.mul continuous_const _,
  norm_cast,
  refine continuous.comp of_real_clm.continuous _,
  refine continuous.pow _ 2,
  refine continuous_norm,},},
  {refine measure_theory.integrable.mul_const _ _,
  convert integrable_schwartz_map (gaussian_complex2 hπδ),},
end



lemma integral_le_3_set_integrals (g : schwartz_map ℝ ℂ) {x δ : ℝ} (hδ : 0 < δ) : 
∀ μ : ℝ, 0< μ →  ∫ (t : ℝ), 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖t‖ ^ 2) * (g.to_fun (x - t) - g.to_fun x) = 
(∫ (x_1 : ℝ) in Iio (-μ), 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖x_1‖ ^ 2) * (g.to_fun (x - x_1) - g.to_fun x)) + (∫ (x_1 : ℝ) in Icc (-μ) μ, 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖x_1‖ ^ 2) * (g.to_fun (x - x_1) - g.to_fun x)) + ∫ (x_1 : ℝ) in Ioi μ, 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖x_1‖ ^ 2) * (g.to_fun (x - x_1) - g.to_fun x) :=
begin
  have h₁: ∀ μ : ℝ, measurable_set (set.Iio (-μ)), by {intro μ,refine measurable_set_Iio,},
  intros μ hμ, 
  have h₂: ∀ μ : ℝ, measurable_set (set.Ioi μ), by {intro μ, refine measurable_set_Ioi,},
  have h₃: (Iio (-μ))ᶜ = (Ici (-μ)), by {simp only [compl_Iio],},
  have h₄: Ici (-μ) = Icc (-μ) (μ) ∪ Ioi (μ), by {rw set.Icc_union_Ioi_eq_Ici, refine neg_le_self (le_of_lt hμ),},
  rw [← measure_theory.integral_add_compl (h₁ μ) _,h₃,h₄,measure_theory.integral_union (Icc_disjoint_Iio (le_of_lt hμ)) (h₂ μ) _ _],
  rw ←add_assoc,
  refine measure_theory.integrable.integrable_on _,
  refine integrable_good_kernel_expression _ hδ,
  refine measure_theory.integrable.integrable_on _,
  refine integrable_good_kernel_expression _ hδ,
  refine integrable_good_kernel_expression _ hδ,
end


lemma good_kernel_rw {g : schwartz_map ℝ ℂ} {x : ℝ} {δ : ℝ} (hδ :0< δ) :  (∫ (t : ℝ), g.to_fun (x - t) * (1 / ↑δ ^ (1 / 2) * cexp (- (real.pi/δ)*‖t‖^2))) - g.to_fun x=∫ (t : ℝ), 1 / ↑δ ^ (1 / 2) * cexp (- (real.pi/δ)*‖t‖^2) * (g.to_fun (x - t) - g.to_fun x) :=
begin
  nth_rewrite 0 ← one_mul (g.to_fun x),
  nth_rewrite 0 ←integral_good_kernel_eq_one hδ, 
  repeat {rw  ← smul_eq_mul,},
  rw [← integral_smul_const, ← measure_theory.integral_sub],
  congr,ext1 t,
  simp_rw mul_comm (g.to_fun (x - t)) _, 
  have : (t: ℂ) ^ 2 = ‖t‖ ^ 2, norm_cast,simp only [norm_eq_abs, pow_bit0_abs],
  rw [smul_eq_mul, mul_sub, this],
  congr,
  {convert integrable_fun1 g hδ,},
  {refine integrable_fun2 g hδ,},
end


-- # part of formalizing corollary 1.7. Uncompleted
lemma tendsto_Iio_zero (g : schwartz_map ℝ ℂ) (δ : ℝ) : 
∀ x : ℝ,tendsto  (λ μ : ℝ, ∫ (y : ℝ) in Iio (-μ), 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖y‖ ^ 2) * (g.to_fun (x - y) - g.to_fun x)) (nhds_within 0 (set.Ioi 0)) (nhds (∫ (y : ℝ) in Iio (-0), 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖y‖ ^ 2) * (g.to_fun (x - y) - g.to_fun x))) :=
begin
  intro x,
  sorry,
end


lemma integral_good_kernel (δ : ℝ) (hδ : 0<δ) : 
∫ (y : ℝ) in Ioi 0, 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖y‖ ^ 2)  = (1 / ↑δ ^ (1 / 2))* ((↑real.pi / (↑real.pi / ↑δ)) ^ ((1: ℂ) / 2) / 2) :=
begin
  simp_rw mul_comm _ (cexp(_)), 
  simp_rw ← smul_eq_mul,
  rw integral_smul_const,
  simp_rw smul_eq_mul,
  have h₄: 0 < ((real.pi: ℂ) / ↑δ).re, by {norm_cast, rw [lt_div_iff hδ, zero_mul], exact pi_pos,},
  have h₅:= integral_gaussian_complex_Ioi h₄,
  rw ← h₅,
  rw mul_comm,
  congr,
  ext1 x,
  norm_cast,simp only [norm_eq_abs, pow_bit0_abs],
end


lemma delta_mu_are_different1 (g : schwartz_map ℝ ℂ) (δ C : ℝ) : 
∀ x : ℝ,tendsto (λ (μ  : ℝ), (∫ (t : ℝ) in Iio (-μ), 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖t‖ ^ 2) * (g.to_fun (x - t) - g.to_fun x)) + ∫ (t : ℝ) in Ioi μ , 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖t‖ ^ 2) * (g.to_fun (x - t) - g.to_fun x)) (nhds_within 0 (Ioi 0)) (nhds ((1 / ↑δ ^ (1 / 2))* ((↑real.pi / (↑real.pi / ↑δ)) ^ ((1: ℂ) / 2) / 2) + (- ((1 / ↑δ ^ (1 / 2))* ((↑real.pi / (↑real.pi / ↑δ)) ^ ((1: ℂ) / 2) / 2))))) :=
begin
  intro x,
  rw metric.tendsto_nhds_within_nhds,
  intros ε hε,
  have h₁:=tendsto_Iio_zero g δ x,
  rw metric.tendsto_nhds_within_nhds at h₁,
  specialize h₁ (ε/2), specialize h₁ _, sorry,
  obtain ⟨e,h₁⟩:=h₁, obtain ⟨he,h₁⟩:=h₁,
  use e, use he,
  intros μ hμ, specialize h₁ hμ,
  intro h, specialize h₁ h,
  rw dist_eq_norm, rw dist_eq_norm at h₁,
  have h₂: ((1 / (δ: ℂ) ^ (1 / 2))* ((↑real.pi / (↑real.pi / ↑δ)) ^ ((1: ℂ) / 2) / 2) + -((1 / ↑δ ^ (1 / 2))* ((↑real.pi / (↑real.pi / ↑δ)) ^ ((1: ℂ) / 2) / 2))) =  ((∫ (y : ℝ) in Iio (-0), 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖y‖ ^ 2) * (g.to_fun (x - y) - g.to_fun x))+(∫ (y : ℝ) in Ioi (0), 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖y‖ ^ 2) * (g.to_fun (x - y) - g.to_fun x))) - (((∫ (y : ℝ) in Iio (-0), 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖y‖ ^ 2) * (g.to_fun (x - y) - g.to_fun x))+(∫ (y : ℝ) in Ioi (0), 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖y‖ ^ 2) * (g.to_fun (x - y) - g.to_fun x))))+ ((1 / (δ: ℂ) ^ (1 / 2))* ((↑real.pi / (↑real.pi / ↑δ)) ^ ((1: ℂ) / 2) / 2) + -((1 / ↑δ ^ (1 / 2))* ((↑real.pi / (↑real.pi / ↑δ)) ^ ((1: ℂ) / 2) / 2))), sorry,
  rw h₂,
  rw sub_add_eq_sub_sub,
  rw ← sub_add,
  rw add_sub_assoc,
  refine lt_of_le_of_lt (norm_add_le _ _) _,
  have h₃: ε = ε/2 + ε/2, ring_nf,
  rw h₃,
  refine add_lt_add _ _,
  convert h₁,
  rw ← integral_good_kernel,
  have h₄: 0 < ((real.pi: ℂ) / ↑δ).re, by {norm_cast, rw zero_lt_mul_right hδ, exact pi_pos,}
  have h₅:= integral_gaussian_complex_Ioi h₄,
  ext1 y,
  dedup,
end

-- # part of formalizing corollary 1.7. Uncompleted
lemma delta_mu_are_different2 (g : schwartz_map ℝ ℂ) (δ C : ℝ) : 
∀ x : ℝ,tendsto (λ (μ  : ℝ), (∫ (t : ℝ) in Iio (-μ), 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖t‖ ^ 2) * (g.to_fun (x - t) - g.to_fun x)) + ∫ (t : ℝ) in Ioi μ , 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖t‖ ^ 2) * (g.to_fun (x - t) - g.to_fun x)) (nhds_within 0 (Ioi 0)) (nhds (C + (-C))) :=
begin
  sorry,
end

lemma delta_is_mixed (g : schwartz_map ℝ ℂ) (C x : ℝ) : 
tendsto (λ (δ : ℝ), (∫ (y : ℝ) in Iio (-δ), 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖y‖ ^ 2) * (g.to_fun (x -y) - g.to_fun x)) + ∫ (y : ℝ) in Ioi δ, 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖y‖ ^ 2) * (g.to_fun (x - y) - g.to_fun x)) (nhds_within 0 (Ioi 0)) (nhds (C + (-C))) :=
begin
  sorry,
end

lemma fourier_convolution_good_kernel_conversion_3part  (g : schwartz_map ℝ ℂ) :
∀ x : ℝ,tendsto (λ (δ : ℝ), (∫ (x_1 : ℝ) in Icc (-δ) δ, 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖x_1‖ ^ 2) * (g.to_fun (x - x_1) - g.to_fun x)) + (∫ (x_1 : ℝ) in Iio (-δ), 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖x_1‖ ^ 2) * (g.to_fun (x - x_1) - g.to_fun x)) +  (∫ (x_1 : ℝ) in Ioi δ, 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖x_1‖ ^ 2) * (g.to_fun (x - x_1) - g.to_fun x))) (nhds_within 0 (Ioi 0)) (nhds 0) := 
begin 
  intro x,
  have h₁: (0: ℂ) = 0 + 0 + 0, rw [add_zero,add_zero],
  rw h₁,
  simp_rw add_assoc,
  refine filter.tendsto.add _ _,
  refine Icc_tendsto_zero1 g x,
  convert delta_is_mixed _ _ _,
  norm_cast,
end


lemma fourier_convolution_good_kernel_conversion0  (g : schwartz_map ℝ ℂ) :
∀ x : ℝ,tendsto (λ δ : ℝ , (∫ (t: ℝ), g.to_fun (x-t) * (λ x : ℝ ,1 / (δ: ℂ) ^ (1 / 2) *complex.exp (- (real.pi/δ)*‖x‖^2))  t) - g.to_fun x) (nhds_within 0 (set.Ioi 0)) (nhds (0)) := 
begin 
  intro x,
  refine tendsto_nhds_within_congr _ _,
  refine λδ : ℝ,((∫ (x_1 : ℝ) in Iio (-δ), 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖x_1‖ ^ 2) * (g.to_fun (x - x_1) - g.to_fun x)) + ∫ (x_1 : ℝ) in Icc (-δ) δ, 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖x_1‖ ^ 2) * (g.to_fun (x - x_1) - g.to_fun x)) + ∫ (x_1 : ℝ) in Ioi δ, 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖x_1‖ ^ 2) * (g.to_fun (x - x_1) - g.to_fun x),
  intros δ hδ,
  rw set.mem_Ioi at hδ,
  have h₁:= integral_le_3_set_integrals g hδ,
  specialize h₁ δ, -- uncompleted
  specialize h₁ hδ,
  rw good_kernel_rw hδ,
  rw h₁,
  convert fourier_convolution_good_kernel_conversion_3part g x,
  ext1 δ,
  repeat {rw ← add_assoc,},
  rw add_comm,
  repeat {rw ← add_assoc,},
  rw add_comm,
  nth_rewrite 0 add_assoc,
  nth_rewrite 1 add_comm,
end


lemma tendsto_sub  (g : schwartz_map ℝ ℂ) :
∀ x : ℝ,tendsto (λ δ : ℝ , ∫ (t: ℝ), g.to_fun (x-t) * (λ x : ℝ ,1 / (δ: ℂ) ^ (1 / 2) *complex.exp (- (real.pi/δ)*‖x‖^2))  t) (nhds_within 0 (set.Ioi 0)) (nhds (g.to_fun x)) := 
begin 
  intro x,
  have h₁:= fourier_convolution_good_kernel_conversion0 g x,
  rw metric.tendsto_nhds_within_nhds,
  rw metric.tendsto_nhds_within_nhds at h₁,
  intros ε hε,
  specialize h₁ ε, specialize h₁ hε,
  obtain ⟨δ,h₁⟩:=h₁, obtain ⟨hδ,h₁⟩:=h₁, 
  use δ,
  split,
  refine hδ,
  intros δ' hδ', 
  specialize h₁ hδ',
  intro h, 
  specialize h₁ h,
  rw dist_eq_norm, rw dist_eq_norm at h₁,
  rw sub_zero at h₁,
  convert h₁,
end


lemma integral_negative (f : ℝ → ℂ) :  ∫ (y : ℝ), f (-y) = ∫ (y : ℝ),  f (y) := 
begin
  refine measure_theory.integral_neg_eq_self _ _,
end

lemma integral_negative_function (g : schwartz_map ℝ ℂ) {δ : ℝ}: 
 ∫ (t : ℝ), g.to_fun (0 - t) * (λ (x : ℝ), 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖x‖ ^ 2)) t = ∫ (t : ℝ), g.to_fun (t) * (λ (x : ℝ), 1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖x‖ ^ 2)) t:=
begin
  simp_rw zero_sub,
  have h₂: ∫ (t : ℝ), g.to_fun (-t) * (1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖t‖ ^ 2))= ∫ (t : ℝ), g.to_fun (-t) * (1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖-t‖ ^ 2)),
    congr, ext1 t, rw norm_neg,
  have h₃: ∫ (t : ℝ), g.to_fun (-t) * (1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖-t‖ ^ 2)) =∫ (t : ℝ), (λt: ℝ,g.to_fun (t) * (1 / ↑δ ^ (1 / 2) * cexp (-(↑real.pi / ↑δ) * ↑‖t‖ ^ 2))) (-t),
    dsimp, congr,
  rw [h₂,h₃,integral_negative],
end


lemma fourier_convolution_good_kernel_conversion2 (g : schwartz_map ℝ ℂ) :
tendsto (λ δ : ℝ ,  ∫ (x : ℝ), g.to_fun x * (𝓕 (λ x : ℝ , complex.exp (-real.pi*δ* ‖x‖^2)) x)) (nhds_within 0 (set.Ioi 0)) (nhds (g.to_fun 0)) := 
begin
  have h₁:= tendsto_sub g 0,
  rw metric.tendsto_nhds_within_nhds,
  rw metric.tendsto_nhds_within_nhds at h₁,
  intros ε hε,  
  specialize h₁ (ε),
  specialize h₁ hε,
  obtain ⟨ξ,h₁⟩:=h₁,
  obtain ⟨hξ ,h₁⟩:=h₁, 
  use ξ,  use hξ,
  intros δ hδ,
  specialize h₁ hδ,
  rw set.mem_Ioi at  hδ,
  intro h,
  specialize h₁ h,
  rw integral_negative_function at h₁,
  convert h₁,
  ext1 x,
  congr,
  have :=good_kernel_fourier_transform x hδ,
  dsimp only at this,
  convert this, 
  ext1 x, congr, norm_cast, rw neg_mul,
  norm_cast,
  simp only [one_div, inv_pow],
  rw sqrt_eq_rpow,
  ring_nf,
end


lemma fourier_convolution_good_kernel_conversion (g : schwartz_map ℝ ℂ) :
tendsto (λ δ : ℝ ,  ∫ (x : ℝ), 𝓕 g.to_fun x * ((λ x : ℝ , complex.exp (-real.pi* δ* ‖x‖^2)) x)) (nhds_within 0 (set.Ioi 0)) (nhds (g.to_fun 0)) := 
begin
  have h₁:= fourier_convolution_good_kernel_conversion2 g,
  rw metric.tendsto_nhds_within_nhds,
  rw metric.tendsto_nhds_within_nhds at h₁,
  intros ε hε,  
  specialize h₁ (ε),
  specialize h₁ hε,
  obtain ⟨ξ,h₁⟩:=h₁,
  obtain ⟨hξ ,h₁⟩:=h₁, 
  use ξ,  use hξ,
  intros δ hδ,
  specialize h₁ hδ,
  rw set.mem_Ioi at  hδ,
  have h₂: ∫ (x : ℝ), 𝓕 g.to_fun x * (λ (x : ℝ), cexp (-↑real.pi*↑δ * ↑‖x‖ ^ 2)) x = ∫ (x : ℝ),  g.to_fun x * 𝓕 (λ (x : ℝ), cexp (-↑real.pi*↑δ * ↑‖x‖ ^ 2)) x,
    {have hδcomplex : 0 < (real.pi*δ: ℂ).re, by {norm_cast, rw zero_lt_mul_right hδ, exact pi_pos,},--simp only [of_real_re], exact hδ,},
    have := multiplication_formula g (gaussian_complex hδcomplex),
    have h₁: (gaussian_complex hδcomplex).to_fun = λ x : ℝ , complex.exp (-(real.pi*δ)* ‖x‖^2), by refl,
    rw h₁ at this,
    have h₂: (λ (x : ℝ), cexp (-↑real.pi * ↑δ * ↑‖x‖ ^ 2)) = (λ (x : ℝ), cexp (-↑(real.pi * δ) * ↑‖x‖ ^ 2)),
      ext1 x, congr, norm_cast, rw neg_mul,
    symmetry,
    convert this, ext1 x, congr,  ext1 x, congr, norm_cast, rw neg_mul,
    ext1 x, congr, dsimp, norm_cast, rw neg_mul,},
  rw h₂,  refine h₁,
end


lemma fourier_inversion {x : ℝ} {δ: ℂ} {hδ : 0<δ.re} (f : schwartz_map ℝ ℂ) : f.to_fun x =∫ (y : ℝ), cexp (↑((2) * real.pi * y * x) * complex.I)* real.fourier_integral f.to_fun y := 
begin 
  set g := (schwartz_add (f) (x)) with hg,
  have hδ': 0 ≠ δ.re,  by {exact ne_of_lt hδ,},
  have h₁: g.to_fun = (λ (y : ℝ), f.to_fun (x + y)), by refl, 
  have h₂: ∀ y : ℝ, g.to_fun y = (λ (y : ℝ), f.to_fun (x + y)) y, by {intro y,rw h₁,}, 
  have h₃: g.to_fun 0 = f.to_fun x, by {dsimp at h₂, convert h₂ 0, rw add_zero,}, 
  have h₄: ∫ (y : ℝ), cexp (↑(2 * real.pi *y*x) * I) * real.fourier_integral f.to_fun y = ∫ (y : ℝ), real.fourier_integral g.to_fun y, 
  by {congr, ext1, rw ← proposition_1_2_i x_1 x f, rw [h₁,fourier_integral_eq_integral_exp_smul, fourier_integral_eq_integral_exp_smul],congr,ext1,rw add_comm,}, 
  rw [← h₃,h₄],
  refine tendsto_nhds_unique (fourier_convolution_good_kernel_conversion g) (converges_proper g),
end

