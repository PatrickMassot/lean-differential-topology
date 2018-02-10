import order.basic

variables {α : Type*} [decidable_linear_order α] variables {β : Type*} [decidable_linear_order β]

lemma max_ge_of_left_ge {a b : α} ( c: α ) (H : a ≤ b ) : a ≤ max b c :=
le_trans H (le_max_left b c)

lemma max_ge_of_right_ge {a c : α} (b :α) (H : a ≤ c) : a ≤ max b c :=
le_trans H (le_max_right b c)

lemma max_monotone_fun {f : α → β} (H : monotone f) (a a' : α) :
max (f a) (f a') =  f(max a a') :=
begin
by_cases a ≤ a',
{ have fa_le_fa' := H h,
  rw max_comm,
  rw max_eq_left fa_le_fa',
  have T :=  max_eq_left h,
  rw max_comm at T,
  rw T },
{ have h' : a' ≤ a := le_of_not_ge h,
  rw max_eq_left (H h'),
  rw  max_eq_left h' }
end

variables {R : Type*} [decidable_linear_ordered_comm_ring R]

lemma monotone_mul_nonneg {a : R} (a_nonneg : 0 ≤ a) : monotone (λ x, a*x) :=
assume b c b_le_c, mul_le_mul_of_nonneg_left b_le_c a_nonneg

lemma max_mul_nonneg {a : R} (b c : R) (a_nonneg : 0 ≤ a) : max (a*b) (a*c) = a*(max b c) :=
max_monotone_fun (monotone_mul_nonneg a_nonneg) b c

lemma max_mul_le_mul_max {a b c d  : R} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd: 0 ≤ d) : 
max (a*b) (c*d) ≤ (max a c) * (max b d) :=
have hac : 0 ≤ max a c := le_trans ha (le_max_left a c),
have AC : a * b ≤ max a c * max b d := mul_le_mul (le_max_left a c) (le_max_left b d) hb hac,
have CD : c * d ≤ max a c * max b d := mul_le_mul (le_max_right a c) (le_max_right b d) hd hac,
max_le AC CD

lemma max_le_max  {a b c d  : R} (h1 : a ≤ b) (h2 : c ≤ d) : max a c ≤ max b d := 
max_le (le_trans h1 (le_max_left b d)) (le_trans h2 (le_max_right b d))