import analysis.metric_space
import ineq

local notation f `→_{`:50 a `}`:0 b := filter.tendsto f (nhds a) (nhds b)

lemma abs_le_max_abs_abs {α : Type*} [decidable_linear_ordered_comm_group α] {a b c : α} :
a ≤ b → b ≤ c → abs b ≤ max (abs a) (abs c) :=
begin
    intros hab hbc,
    apply abs_le_of_le_of_neg_le,
    { exact (calc
        b ≤ c : hbc
        ... ≤ abs c : le_abs_self _
        ... ≤ max (abs a) (abs c): le_max_right _ _) },
    { exact (calc
        -b ≤ -a : neg_le_neg hab
        ... ≤ abs a : neg_le_abs_self _
        ... ≤ max (abs a) (abs c): le_max_left _ _) }
end

lemma squeeze {X : Type*} [metric_space X] (f g h : X → ℝ) (x₀ : X) (y : ℝ): 
(∀ x : X, f x ≤ g x) → (∀ x : X, g x ≤ h x) → (f →_{x₀} y) → (h →_{x₀} y) → (g →_{x₀} y) :=
begin
    intros ineq_fg ineq_gh lim_f lim_h,
    apply  tendsto_nhds_of_metric.2,
    intros ε ε_pos,
    rcases (tendsto_nhds_of_metric.1 lim_f ε ε_pos) with ⟨δ_f, δ_f_pos, ineq_lim_f⟩,
    rcases (tendsto_nhds_of_metric.1 lim_h ε ε_pos) with ⟨δ_h, δ_h_pos, ineq_lim_h⟩,
    existsi (min δ_f δ_h),
    existsi lt_min δ_f_pos δ_h_pos,
    intros x dist_x,

    have abs_f_x : dist (f x) y < ε := 
    ineq_lim_f (calc
        dist x x₀ < min δ_f δ_h : by assumption
            ... ≤ δ_f :  min_le_left _ _),

    have abs_h_x : dist (h x) y < ε := 
    ineq_lim_h (calc
        dist x x₀ < min δ_f δ_h : by assumption
            ... ≤ δ_h :  min_le_right _ _),

    have ineq_fg_y : f x - y ≤ g x - y := 
        (sub_le_sub_iff_right y).2 (ineq_fg x),

    have ineq_gh_y : g x - y ≤ h x - y :=
        (sub_le_sub_iff_right y).2 (ineq_gh x),

    exact calc 
        dist (g x) y = abs (g x - y) : rfl
        ... ≤ max (abs (f x - y)) (abs (h x - y)) : by { apply abs_le_max_abs_abs; assumption }
        ... < ε :  by { apply max_lt ; assumption }
end