import analysis.real
import analysis.metric_space
import analysis.limits
import algebra.module
import order.filter

noncomputable theory
local attribute [instance] classical.prop_decidable

-- This will soon be bultin mathlib
attribute [simp] abs_zero abs_neg

def goesto {α β : Type*} [topological_space α] [topological_space β] (f : α → β) (a : α) (b : β) : Prop :=
filter.tendsto f (nhds a) (nhds b)

local notation f `→_{` a `}` b := goesto f a b

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
lemma zero_norm' {E : Type*} [normed_space E] : ∥0∥ = 0 :=
sorry


instance normed_space.to_metric_space {A : Type*} [An : normed_space A] : metric_space A :=
metric_of_norm An.norm


section continuous_linear_maps
variables {E : Type*} {F : Type*} {G : Type*} [normed_space E] [normed_space F] [normed_space G]

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
end continuous_linear_maps

section differential
variables {E : Type*} {F : Type*} {G : Type*} [normed_space E] [normed_space F] [normed_space G]

def is_differential  (f : E → F) (a : E) (L : E → F) : Prop :=
(is_continuous_linear_map L) ∧ (∃ ε : E → F, (∀ h, f (a + h) =  f a + L h + ∥h∥ • ε h) ∧  (ε →_{0} 0))

 set_option trace.check true
 set_option pp.all true

theorem chain_rule (f : E → F) (g : F → G) (a : E) (L : E → F) (P : F → G)
(D : is_differential f a L) (D' : is_differential g (f a) P) : is_differential (g ∘ f) a (P ∘ L) :=
begin
rcases D with ⟨cont_lin_L, ε, TEf, lim_ε⟩,
rcases D' with ⟨cont_lin_P, η, TEg, lim_η⟩,
unfold is_differential,
split,
{ exact comp_continuous_linear_map L P cont_lin_L cont_lin_P },
let δ : E → G,-- := λ h, P (ε h) + (∥ L h + ∥h∥•ε h ∥/∥h∥)• η (L h + ∥h∥•ε h),
swap,
existsi δ,
{ split,
  { intro h,
    by_cases H : h = 0,
    { -- h = 0 case
      simp [H],
      rw [@zero_norm' E _], -- or variations that also don't work
      
      admit },
    { -- h ≠ 0 case
      rcases cont_lin_P with ⟨lin_P , cont_P⟩,
       
      have fact1 := calc 
      (g ∘ f) (a + h) = g (f (a + h)): by refl
      ... = g (f a + L h + ∥h∥ • ε h)  : by rw TEf
      ... = g (f a + (L h + ∥h∥ • ε h)) : by {simp, }
      ... = g (f a) + P (L h + ∥h∥ • ε h) + ∥ L h + ∥h∥ • ε h∥ • η (L h + ∥h∥ • ε h) : by rw TEg
      ... = g (f a) + P (L h) + ∥h∥ • P (ε h) + ∥ L h + ∥h∥ • ε h∥ • η (L h + ∥h∥ • ε h) : by { simp[lin_P.add, lin_P.smul] },

  
    repeat {rw add_assoc},
    apply (congr_arg (λ x, g (f a) + (P (L h) + x))),
    dsimp[δ], 
    generalize : L h + ∥h∥ • ε h = R,
    rw smul_add,
    apply (congr_arg (λ x, ∥h∥ • P (ε h) + x)),
    rw smul_smul,
    congr,
        
    admit },
  { admit }, },
end

end differential