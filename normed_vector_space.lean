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

variables {E : Type*} {F : Type*} {G : Type*} [normed_space E] [normed_space F] [normed_space G]

def norm : E → ℝ := normed_space.norm E
local notation `∥` e `∥` := norm e

@[simp]
lemma zero_norm' : ∥(0:E)∥ = 0 :=
zero_norm _

lemma non_neg_norm : ∀ e : E, 0 ≤ ∥e∥ :=
vector_space_norm.nonneg _

lemma norm_non_zero_of_non_zero (e : E) : e ≠ 0 → ∥ e ∥ ≠ 0 :=
not_imp_not.2 (vector_space_norm.eq_zero _ _)

lemma norm_pos_of_non_zero (e : E) : e ≠ 0 → ∥ e ∥ > 0 :=
assume e_non_zero, lt_of_le_of_ne (non_neg_norm _) (ne.symm (norm_non_zero_of_non_zero e e_non_zero))

lemma triangle_ineq (a b : E) : ∥ a + b ∥ ≤ ∥ a ∥ + ∥ b ∥ :=
vector_space_norm.triangle _ _ _

lemma homogeneity (a : E) (s : ℝ): ∥ s • a ∥ = (abs s)* ∥ a ∥ :=
vector_space_norm.homo _ _ _


section normed_space_topology

instance normed_space.to_metric_space {A : Type*} [An : normed_space A] : metric_space A :=
metric_of_norm An.norm

instance normed_top_monoid  : topological_add_monoid E  := 
sorry


lemma tendsto_iff_norm_tends_to_zero (f : E → F) (a : E) (b : F) : (f →_{a} b) ↔ ((λ e, ∥ f e - b ∥) →_{a} 0) :=
sorry

lemma squeeze_zero {T : Type*} [topological_space T] (f g : T → ℝ) (t₀ : T) : 
(∀ t : T, 0 ≤ f t) → (∀ t : T, f t ≤ g t) → (g →_{t₀} 0) → (f →_{t₀} 0) :=
sorry

lemma lim_norm (E : Type*) [normed_space E] : ((λ e, ∥e∥) : E → ℝ) →_{0} 0 :=
sorry

lemma tendsto_smul {f : E → ℝ} { g : E → F} {e : E} {s : ℝ} {b : F} :
(f →_{e} s) → (g →_{e} b) → ((λ e, (f e) • (g e)) →_{e} s • b) := 
sorry

end normed_space_topology

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

