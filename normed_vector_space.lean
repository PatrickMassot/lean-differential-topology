import analysis.real
import analysis.metric_space

noncomputable theory

attribute [simp] abs_zero abs_neg

variables {E : Type*} [vector_space ℝ E]

structure is_norm (N : E → ℝ) : Prop :=
  (nonneg : ∀ e : E, 0 ≤ N e)
  (eq_zero : ∀ e : E, N e = 0 → e = 0)
  (triangle : ∀ e f : E, N (e + f) ≤ N e + N f)
  (homo : ∀ l : ℝ, ∀ e : E, N (l • e) = abs(l) * N e)

lemma zero_norm (N : E → ℝ) (H : is_norm N) : N 0 = 0 :=
by simpa using H.homo 0 0

lemma abs1 : abs (1:ℝ) = 1 :=
abs_of_pos zero_lt_one

instance metric_of_norm {E : Type*} [vector_space ℝ E] {N : E → ℝ} (H : is_norm N) : metric_space E :=
{ dist := λ x y, N (x - y),
  dist_self := by  simp [H, zero_norm N],
  eq_of_dist_eq_zero := assume x y N0, eq_of_sub_eq_zero (H.eq_zero _ N0),
  dist_comm := assume x y, by simpa [abs1] using (H.homo (-1:ℝ) (x -y)).symm,
  dist_triangle := assume x y z, by simpa using H.triangle (x-y) (y-z) }

structure norm (E : Type*) [vector_space ℝ E] :=
  (map : E → ℝ)
  (nonneg : ∀ e : E, 0 ≤ map e)
  (eq_zero : ∀ e : E, map e = 0 → e = 0)
  (triangle : ∀ e f : E, map (e + f) ≤ map e + map f)
  (homo : ∀ l : ℝ, ∀ e : E, map (l • e) = abs(l) * map e)

instance : has_coe_to_fun (norm E) := 
⟨_, norm.map⟩

@[simp]
lemma zero_norm' (N : norm E) : N 0 = 0 :=
by simpa using N.homo 0 0

instance metric_of_norm' {E : Type*} [vector_space ℝ E] {N : norm E} : metric_space E :=
{ dist := λ x y, N (x - y),
  dist_self := by simp,
  eq_of_dist_eq_zero := assume x y N0, eq_of_sub_eq_zero (N.eq_zero _ N0),
  dist_comm := assume x y, by simpa [abs1] using (N.homo (-1:ℝ) (x -y)).symm,
  dist_triangle := assume x y z, by simpa using N.triangle (x-y) (y-z) }