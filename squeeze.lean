import analysis.metric_space
import ineq

local notation f `→_{`:50 a `}`:0 b := filter.tendsto f (nhds a) (nhds b)


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

have := min_le_left δ_f δ_h,
have dist_x_δ_f : dist x x₀ < δ_f,
ineq_trans, clear this,
have abs_f_x := ineq_lim_f dist_x_δ_f, clear dist_x_δ_f,
rw [show dist (f x) y = abs (f x - y), from rfl] at abs_f_x,

have := min_le_right δ_f δ_h,
have dist_x_δ_h : dist x x₀ < δ_h,
ineq_trans, clear this,

have abs_h_x := ineq_lim_h dist_x_δ_h, clear dist_x_δ_h,
rw [show dist (h x) y = abs (h x - y), from rfl] at abs_h_x,

have sub_f_gt := (abs_lt.1 abs_f_x).left,
have tmp := (sub_le_sub_iff_right y).2 (ineq_fg x),
have g_gt : -ε < g x - y
--, ineq_trans,  Does not work :(
 := lt_of_lt_of_le sub_f_gt tmp,

have sub_h_lt := (abs_lt.1 abs_h_x).right,
have tmp2 := (sub_le_sub_iff_right y).2 (ineq_gh x),
have g_lt : g x - y < ε := lt_of_le_of_lt tmp2 sub_h_lt,

exact abs_lt.2 ⟨g_gt, g_lt⟩
end