import algebra.group
import analysis.metric_space


class normed_group (α : Type*) extends add_comm_group α, metric_space α :=
(norm : α → ℝ)
(dist_eq : ∀ x y, dist x y = norm (x - y))

section normed_group
def norm {G : Type*} [normed_group G] : G → ℝ := normed_group.norm 
local notation `∥` e `∥` := norm e

variables {G : Type*} [nG : normed_group G]
-- Following seems necessary, Lean is not smart enough here?
include nG

-- The following tries to replace two steps that arise in all proofs. But it doesn't work
-- I'd be happy to learn how to do that (although in this case it's not a big benefit)
-- One could almost imagine a mechanism like the one translating multiplicative lemmas to additive ones
meta def translate_to_dist : tactic unit := do
`[unfold norm], 
`[rw[←nG.dist_eq]]


-- In the next proof, I'm not sure why all those unfold are necessary
-- Also not sure naming nG is necessary (same question in other proofs)
-- About which arguments are implicit, I followed metric_space.lean, without really understanding
lemma norm_triangle (g h : G) : ∥g + h∥ ≤ ∥g∥ + ∥h∥ :=
calc 
∥g + h∥ = ∥g - (-h)∥             : by simp
   ... = dist g (-h)            : by { unfold norm, rw [←nG.dist_eq], refl }
   ... ≤ dist g 0 + dist 0 (-h) : by apply nG.dist_triangle
   ... = ∥g∥ + ∥h∥               : by { unfold dist, repeat {rw[nG.dist_eq]}, simp, refl }

lemma norm_nonneg {g : G} : 0 ≤ ∥g∥ :=
begin
  rw[show ∥g∥ = ∥g-0∥, by simp],
  unfold norm, rw[←nG.dist_eq],
  exact dist_nonneg
end

-- Not sure whether it would be more convenient to have one lemma per implication
lemma norm_zero_iff_zero {g : G} : ∥g∥ = 0 ↔ g = 0 :=
begin
  rw[show ∥g∥ = ∥g-0∥, by simp],
  unfold norm, rw[←nG.dist_eq],
  exact dist_eq_zero_iff
end

lemma norm_pos_of_ne {g : G} (h : g ≠ 0) : ∥ g ∥  > 0 :=
begin
  rw[show ∥g∥ = ∥g-0∥, by simp],
  unfold norm, rw[←nG.dist_eq],
  exact dist_pos_of_ne h
end

lemma norm_le_zero_iff {g : G} : ∥g∥ ≤ 0 ↔ g = 0 :=
begin
  rw[show ∥g∥ = ∥g-0∥, by simp],
  unfold norm, rw[←nG.dist_eq],
  exact dist_le_zero_iff
end


lemma ne_of_norm_pos {g : G} (h : ∥g∥ > 0) : g ≠ 0 :=
begin
  rw[show ∥g∥ = ∥g-0∥, by simp] at h,
  unfold norm at h, rw[←nG.dist_eq] at h,
  exact ne_of_dist_pos h
end

lemma eq_norm_of_neg {g : G} : ∥g∥ = ∥-g∥ :=
begin
  rw[show ∥g∥ = ∥g-0∥, by simp],
  rw[show ∥-g∥ = ∥0-g∥, by simp],
  unfold norm, repeat {rw[←nG.dist_eq]},
  -- I would like to write the following but can't
  -- exact nG.dist_comm g 0
  have := nG.dist_comm,
  specialize this g 0,
  exact this
end

end normed_group

class normed_ring (α : Type*) extends ring α, metric_space α :=
(norm : α → ℝ)
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul : ∀ a b, norm (a * b) = norm a * norm b)

variables {α : Type*} {β : Type*}

instance normed_ring.to_normed_group [H : normed_ring α] : normed_group α :=
{ to_uniform_space := H.to_uniform_space, ..H }

class normed_field (α : Type*) extends discrete_field α, metric_space α :=
(norm : α → ℝ)
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul : ∀ a b, norm (a * b) = norm a * norm b)

instance normed_field.to_normed_ring [H : normed_field α] : normed_ring α :=
{ to_uniform_space := H.to_uniform_space, ..H }

class normed_space (α β : Type*) [normed_field α] extends vector_space α β, metric_space β :=
(norm : β → ℝ)
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_smul : ∀ a b, norm (a • b) = normed_field.norm a * norm b)

instance normed_space.to_normed_group [normed_field α] [H : normed_space α β] : normed_group β :=
{ to_uniform_space := H.to_uniform_space, ..H }