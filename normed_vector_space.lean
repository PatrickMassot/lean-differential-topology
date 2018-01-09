import analysis.real
import analysis.metric_space
import analysis.limits
import analysis.topology.continuity
import analysis.topology.topological_structures
import algebra.module
import order.filter

noncomputable theory
local attribute [instance] classical.prop_decidable

-- This will soon be bultin mathlib
attribute [simp] abs_zero abs_neg


--local notation f `→_{` a `}` b := filter.tendsto f (nhds a) (nhds b)
local notation f `→_{`:50 a `}`:0 b := filter.tendsto f (nhds a) (nhds b)

lemma abs1 : abs (1:ℝ) = 1 :=
abs_of_pos zero_lt_one


variables {V : Type*} [vector_space ℝ V]

structure vector_space_norm (V : Type*) [vector_space ℝ V] :=
  (map : V → ℝ)
  (nonneg : ∀ e : V, 0 ≤ map e)
  (eq_zero : ∀ e : V, map e = 0 → e = 0)
  (triangle : ∀ e f : V, map (e + f) ≤ map e + map f)
  (homo : ∀ l : ℝ, ∀ e : V, map (l • e) = abs(l) * map e)

instance : has_coe_to_fun (vector_space_norm V) := 
⟨_, vector_space_norm.map⟩

@[simp]
lemma zero_norm (N : vector_space_norm V) : N 0 = 0 :=
by simpa using N.homo 0 0


def metric_of_norm {V : Type*} [vector_space ℝ V] (N : vector_space_norm V) : metric_space V :=
{ dist := λ x y, N (x - y),
  dist_self := by simp,
  eq_of_dist_eq_zero := assume x y N0, eq_of_sub_eq_zero (N.eq_zero _ N0),
  dist_comm := assume x y, by simpa [abs1] using (N.homo (-1:ℝ) (x -y)).symm,
  dist_triangle := assume x y z, by simpa using N.triangle (x-y) (y-z) }

class normed_space (type : Type*) extends vector_space ℝ type :=
(norm : vector_space_norm type)

def norm {E : Type*} [normed_space E] : E → ℝ := normed_space.norm E
local notation `∥` e `∥` := norm e



@[simp]
lemma zero_norm' {E : Type*} [normed_space E] : ∥(0:E)∥ = 0 :=
sorry
lemma non_neg_norm {E : Type*} [normed_space E] : ∀ e : E, 0 ≤ ∥e∥ :=
sorry

lemma norm_non_zero_of_non_zero {E : Type*} [normed_space E] (e : E) : e ≠ 0 → ∥ e ∥ ≠ 0 :=
sorry 

lemma triangle_ineq {E : Type*} [normed_space E] (a b : E) : ∥ a + b ∥ ≤ ∥ a ∥ + ∥ b ∥ :=
sorry

lemma homogeneity {E : Type*} [normed_space E] (a : E) (s : ℝ): ∥ s • a ∥ = (abs s)* ∥ a ∥ :=
sorry

instance normed_space.to_metric_space {A : Type*} [An : normed_space A] : metric_space A :=
metric_of_norm An.norm

instance normed_top_monoid  {E : Type*} [normed_space E] : topological_add_monoid E  := sorry

variables {E : Type*} {F : Type*} {G : Type*} [normed_space E] [normed_space F] [normed_space G]

lemma tendsto_iff_norm_tends_to_zero (f : E → F) (a : E) (b : F) : (f →_{a} b) ↔ ((λ e, ∥ f e - b ∥) →_{a} 0) :=
sorry

lemma squeeze_zero {T : Type*} [topological_space T] (f g : T → ℝ) (t₀ : T) : 
(∀ t : T, 0 ≤ f t) → (∀ t : T, f t ≤ g t) → (g →_{t₀} 0) → (f →_{t₀} 0) :=
sorry

lemma lim_norm (E : Type*) [normed_space E] : ((λ e, ∥e∥) : E → ℝ) →_{0} 0 :=
sorry

lemma tendsto_smul {E : Type*} [normed_space E] {f : E → ℝ} { g : E → F} {e : E} {s : ℝ} {b : F} :
(f →_{e} s) → (g →_{e} b) → ((λ e, (f e) • (g e)) →_{e} s • b) := 
sorry

section continuous_linear_maps

-- TODO: relate to is_continuous
def is_continuous_linear_map (L : E → F) := (is_linear_map L) ∧  ∃ M, M > 0 ∧ ∀ x : E, ∥ L x ∥ ≤ M *∥ x ∥ 

-- TODO: Clean up this proof
lemma comp_continuous_linear_map (L : E → F) (P : F → G) : 
is_continuous_linear_map L → is_continuous_linear_map P → is_continuous_linear_map (P ∘ L) :=
begin
intros HL HP,
rcases HL with ⟨lin_L , M, Mpos, ineq_L⟩,
rcases HP with ⟨lin_P , M', M'pos, ineq_P⟩,
split,
{ exact is_linear_map.comp lin_P lin_L },
{ existsi M*M',
  split,
  { exact mul_pos Mpos M'pos },
  { unfold function.comp,
    intro x,
    specialize ineq_P (L x),
    specialize ineq_L x,
    have fact : M'*∥L x∥ ≤ M * M' * ∥x∥ := -- prepare for PAIN
      begin 
      have ineq := mul_le_mul_of_nonneg_left ineq_L (le_of_lt M'pos),
      rw mul_comm, 
      rw mul_comm at ineq, 
      rw ←mul_assoc at ineq,
      rw mul_comm M,  
      exact ineq
      end ,
    exact le_trans ineq_P fact }
   }
end

lemma lim_zero_cont_lin_map (L : E → F) : is_continuous_linear_map L → (L →_{0} 0) :=
sorry

end continuous_linear_maps




-- set_option trace.class_instances true
example (f g : E → F) : (f →_{0} 0) → (g →_{0} 0) → ((λ x, f x + g x) →_{0} 0) :=
begin
intros Hf Hg,
have := tendsto_add Hf Hg,
simp at this,
exact this,
end


section differential
def is_differential  (f : E → F) (a : E) (L : E → F) : Prop :=
(is_continuous_linear_map L) ∧ (∃ ε : E → F, (∀ h, f (a + h) =  f a + L h + ∥h∥ • ε h) ∧  (ε →_{0} 0))

-- set_option trace.check true
-- set_option trace.class_instances true
-- set_option pp.all true

open filter

theorem chain_rule (f : E → F) (g : F → G) (a : E) (L : E → F) (P : F → G)
(D : is_differential f a L) (D' : is_differential g (f a) P) : is_differential (g ∘ f) a (P ∘ L) :=
begin
rcases D with ⟨cont_lin_L, ε, TEf, lim_ε⟩,
rcases D' with ⟨cont_lin_P, η, TEg, lim_η⟩,
unfold is_differential,
have cont_linPL := comp_continuous_linear_map L P cont_lin_L cont_lin_P,
split,
{ exact cont_linPL },
let δ := λ h, if (h = 0) then 0 else  P (ε h) + (∥ L h + ∥h∥•ε h ∥/∥h∥)• η (L h + ∥h∥•ε h),
swap,
{existsi δ,
{ split; rcases cont_lin_P with ⟨lin_P , MP, MP_pos, ineq_P⟩; rcases cont_lin_L with ⟨lin_L , ML, ML_pos, ineq_L⟩,
  { intro h,
    by_cases H : h = 0,
    { -- h = 0 case
      simp [H, cont_linPL.1.zero] },
    { -- h ≠ 0 case
      have fact1 := calc 
      (g ∘ f) (a + h) = g (f (a + h)): by refl
      ... = g (f a + L h + ∥h∥ • ε h)  : by rw TEf
      ... = g (f a + (L h + ∥h∥ • ε h)) : by {simp, }
      ... = g (f a) + P (L h + ∥h∥ • ε h) + ∥ L h + ∥h∥ • ε h∥ • η (L h + ∥h∥ • ε h) : by rw TEg
      ... = g (f a) + P (L h) + ∥h∥ • P (ε h) + ∥ L h + ∥h∥ • ε h∥ • η (L h + ∥h∥ • ε h) : by { simp[lin_P.add, lin_P.smul] },
      
      simp[δ, H, fact1], 
      -- now we only need computing and h ≠ 0
      clear fact1 lin_L ineq_L ML_pos ML lin_P ineq_P MP_pos MP cont_linPL δ TEf TEg f g lim_ε lim_η a,
      
      rw[smul_add, smul_smul],
      congr_n 1,
      apply (congr_arg (λ x, x • η (L h + ∥h∥ • ε h))),
            
      rw [←mul_div_assoc, mul_comm, mul_div_cancel],
      
      exact norm_non_zero_of_non_zero h H },
  }, 
  { -- prove δ →_0 0
    have norm_reformulation:= (tendsto_iff_norm_tends_to_zero δ 0 0).2,
    simp at norm_reformulation,
    apply norm_reformulation, clear norm_reformulation,
    
    have bound_δ : ∀ h :E, ∥ δ h ∥ ≤ MP*∥ε h∥ + ( ML + ∥ε h ∥)*∥ η (L h + ∥h∥•ε h)∥,
    { intro h,
      by_cases H : h = 0,
      { -- h = 0 case
       simp [H, δ],
       simp,
       
       have h1 : 0 ≤ MP * ∥ε 0∥ := mul_nonneg (le_of_lt MP_pos) (non_neg_norm (ε 0)),
       have h2 : 0 ≤ ML + ∥ε 0∥ := add_nonneg' (le_of_lt ML_pos) (non_neg_norm (ε 0)),
       have h3 : 0 ≤ (ML + ∥ε 0∥) * ∥η (L 0)∥ := mul_nonneg h2 (non_neg_norm (η (L 0))),
             
       exact add_nonneg' h1 h3 },
      { -- h ≠ 0 case
        simp [δ],
        simp [H],

        have prelim : (∥L h∥ + ∥h∥ * ∥ε h∥) / ∥h∥ * ∥η (L h + ∥h∥ • ε h)∥ ≤
         (ML * ∥h∥ + ∥h∥ * ∥ε h∥) / ∥h∥ * ∥η (L h + ∥h∥ • ε h)∥ := sorry,
        exact calc 
        ∥P (ε h) + (∥L h + ∥h∥ • ε h∥ / ∥h∥) • η (L h + ∥h∥ • ε h)∥ ≤ ∥P (ε h)∥  +  ∥ (∥L h + ∥h∥ • ε h∥ / ∥h∥) • η (L h + ∥h∥ • ε h)∥ : by { simp[triangle_ineq] }
        ... ≤ MP*∥ε h∥ + ∥ (∥L h + ∥h∥ • ε h∥ / ∥h∥) • η (L h + ∥h∥ • ε h)∥ : by { simp[ineq_P] }
        ... ≤ MP*∥ε h∥ + (∥L h + ∥h∥ • ε h∥ / ∥h∥) * ∥ η (L h + ∥h∥ • ε h)∥ : by { simp[homogeneity], admit }
        ... ≤ MP*∥ε h∥ + ((∥L h∥ + ∥ ∥h∥ • ε h∥) / ∥h∥) * ∥ η (L h + ∥h∥ • ε h)∥ : by { simp[triangle_ineq], admit }
        ... ≤ MP*∥ε h∥ + ((∥L h∥ +  ∥h∥ *∥ε h∥) / ∥h∥) * ∥ η (L h + ∥h∥ • ε h)∥ : by { simp[homogeneity, abs_of_nonneg (non_neg_norm h)],  admit }
        ... ≤ MP*∥ε h∥ + ((ML*∥h∥ +  ∥h∥ *∥ε h∥) / ∥h∥) * ∥ η (L h + ∥h∥ • ε h)∥ : by {simp[prelim] }
        ... ≤ MP*∥ε h∥ + (ML +  ∥ε h∥) * ∥ η (L h + ∥h∥ • ε h)∥ : by { simp[add_div, mul_div_cancel, H], admit  }
        ... ≤ MP*∥ε h∥ + (ML + ∥ε h∥) * ∥ η (L h + ∥h∥ • ε h)∥ : by { admit },
        } },
    
     
    have norm_δ_nonneg : ∀ (t : E), (0:ℝ) ≤ (λ (h : E), ∥δ h∥) t :=
    assume t,non_neg_norm (δ t),
    
    apply squeeze_zero (λ h, ∥ δ h∥) (λ h, MP*∥ε h∥ + ( ML + ∥ε h ∥)*∥ η (L h + ∥h∥•ε h)∥) 0 norm_δ_nonneg bound_δ,
    clear norm_δ_nonneg bound_δ, 

    have limML : ((λ (x: E), ML) →_{0} ML) := tendsto_const_nhds,
      
    have lim_normE:= lim_norm E,
    have lim_ML_norm := tendsto_mul limML lim_normE,
    simp at lim_ML_norm,

    have lim1 : ((λ (h: E),  L h + ∥h∥ • ε h) →_{(0:E)} 0),
    { 
      have := squeeze_zero (λ (x : E), ∥L x∥) (λ (x : E), ML*∥x∥) 0,
      simp[non_neg_norm, ineq_L] at this, clear ineq_L,
      
      simp[lim_ML_norm] at this,
      rename this lim_norm_L,
      have lim_L := (tendsto_iff_norm_tends_to_zero L 0 0).2,
      simp at lim_L,
      specialize lim_L lim_norm_L,
      
      simpa using tendsto_add lim_L (tendsto_smul lim_normE lim_ε) },
      
    
    have lim2 := tendsto_compose lim1 lim_η, clear lim1,

    have norm_reformulation := (tendsto_iff_norm_tends_to_zero (λ (h: E),  η (L h + ∥h∥ • ε h)) 0 0 ).1,
    simp at norm_reformulation,
    
    have lim3 : ((λ (h: E),  ∥ η (L h + ∥h∥ • ε h)∥) →_{0} (0)) :=
    norm_reformulation lim2, clear norm_reformulation, clear lim2,
    
    have lim_norm_ε : (λ (e : E), ∥ε e∥)→_{0}0 := 
    by simpa using (tendsto_iff_norm_tends_to_zero ε 0 0 ).1 lim_ε,
    have lim4 : (λ (x : E),  ML + ∥ε x∥)→_{0} ML := 
    by simpa using tendsto_add limML lim_norm_ε,
    
    have lim5 : (λ (x : E), (∥ε x∥ + ML) * ∥η (L x + ∥x∥ • ε x)∥)→_{0}0 :=
    by simpa using tendsto_mul lim4 lim3,
    
    have limMP : ((λ (x: E), MP) →_{0} MP) := tendsto_const_nhds,
    
    have lim6 := tendsto_mul limMP lim_norm_ε,
    simp at lim6,

    have lim7:= tendsto_add lim6 lim5,
    simp at lim7,
    
    simp [lim7] } } }
end

end differential