import analysis.real
import analysis.metric_space
import analysis.limits
import algebra.module

noncomputable theory

-- This will soon be bultin mathlib
attribute [simp] abs_zero abs_neg

def goesto {α β : Type*} [topological_space α] [topological_space β] (f : α → β) (a : α) (b : β) : Prop :=
filter.tendsto f (nhds a) (nhds b)

local notation f `→_{` a `}` b := goesto f a b

lemma abs1 : abs (1:ℝ) = 1 :=
abs_of_pos zero_lt_one


variables {E : Type*} [vector_space ℝ E]

structure vector_space_norm (E : Type*) [vector_space ℝ E] :=
  (map : E → ℝ)
  (nonneg : ∀ e : E, 0 ≤ map e)
  (eq_zero : ∀ e : E, map e = 0 → e = 0)
  (triangle : ∀ e f : E, map (e + f) ≤ map e + map f)
  (homo : ∀ l : ℝ, ∀ e : E, map (l • e) = abs(l) * map e)

instance : has_coe_to_fun (vector_space_norm E) := 
⟨_, vector_space_norm.map⟩

@[simp]
lemma zero_norm (N : vector_space_norm E) : N 0 = 0 :=
by simpa using N.homo 0 0


def metric_of_norm {E : Type*} [vector_space ℝ E] (N : vector_space_norm E) : metric_space E :=
{ dist := λ x y, N (x - y),
  dist_self := by simp,
  eq_of_dist_eq_zero := assume x y N0, eq_of_sub_eq_zero (N.eq_zero _ N0),
  dist_comm := assume x y, by simpa [abs1] using (N.homo (-1:ℝ) (x -y)).symm,
  dist_triangle := assume x y z, by simpa using N.triangle (x-y) (y-z) }

class normed_space (type : Type*) extends vector_space ℝ type :=
(norm : vector_space_norm type)

def norm {F : Type*} [nF : normed_space F] : F → ℝ := normed_space.norm F

instance normed_space.to_metric_space {A : Type*} [An : normed_space A] : metric_space A :=
metric_of_norm An.norm

def is_differential {E F : Type*} [nE : normed_space E] [nF : normed_space F] (f : E → F) (a : E) (L : E → F) (H: is_linear_map L) : Prop :=
(λ x, (1/(norm (x - a))) • (f x - f a - (L (x -a)))) →_{a} 0