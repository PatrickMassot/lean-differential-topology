import analysis.metric_space

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

lemma squeeze_zero {T : Type*} [metric_space T] (f g : T → ℝ) (t₀ : T) : 
(∀ t : T, 0 ≤ f t) → (∀ t : T, f t ≤ g t) → (g →_{t₀} 0) → (f →_{t₀} 0) :=
assume f_non_neg f_le_g,  squeeze (λ t : T, 0) f g t₀ 0 f_non_neg f_le_g tendsto_const_nhds
