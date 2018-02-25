import algebra.module

-- following does not work, always need (x[i])
-- local notation x`[`:max i`]`:0 := x i
-- it would be nice to have a notation making it clear we don't think of x as a function

namespace indexed_product
universes u v
variable {I : Type u} -- The indexing type
variable {f : I → Type v}

instance has_mul [∀ i, has_mul $ f i] : has_mul (Π i : I, f i) := 
⟨λ x y, λ i, x i * y i⟩

instance semigroup [∀ i, semigroup $ f i] : semigroup (Π i : I, f i) :=
{ mul_assoc := assume a b c, by funext ; exact @semigroup.mul_assoc (f i) _ (a i) (b i) (c i),
  ..indexed_product.has_mul }

instance comm_semigroup [∀ i, comm_semigroup $ f i] : comm_semigroup (Π i : I, f i) :=
{ mul_comm := assume a b, by funext ; exact @comm_semigroup.mul_comm (f i) _ (a i) (b i),
  ..indexed_product.semigroup }

instance has_one [∀ i, has_one $ f i] : has_one (Π i : I, f i) := 
⟨λ i, 1⟩

instance has_inv [∀ i, has_inv $ f i] : has_inv (Π i : I, f i) := 
⟨λ x, λ i, (x i)⁻¹⟩

instance monoid [∀ i, monoid $ f i] : monoid (Π i : I, f i) :=
{ one_mul := assume a, by funext ; exact @monoid.one_mul (f i) _ (a i),
  mul_one := assume a, by funext ; exact @monoid.mul_one (f i) _ (a i),
  ..indexed_product.has_one,
  ..indexed_product.has_inv,
  ..indexed_product.semigroup }

instance comm_monoid [∀ i, comm_monoid $ f i] : comm_monoid (Π i : I, f i) :=
{ ..indexed_product.monoid,
  ..indexed_product.comm_semigroup }

instance group [∀ i, group $ f i] : group (Π i : I, f i) :=
{ mul_left_inv := assume a, by funext ; exact @group.mul_left_inv (f i) _ (a i),
  ..indexed_product.has_inv,
  ..indexed_product.monoid }


instance has_add [∀ i, has_add $ f i] : has_add (Π i : I, f i) := 
⟨λ x y, λ i, x i + y i⟩

instance add_semigroup [∀ i, add_semigroup $ f i] : add_semigroup (Π i : I, f i) :=
{ add_assoc := assume a b c, by funext ; exact @add_semigroup.add_assoc (f i) _ (a i) (b i) (c i),
  ..indexed_product.has_add }

instance has_zero [∀ i, has_zero $ f i] : has_zero (Π i : I, f i) := 
⟨λ i, 0⟩

instance has_neg [∀ i, has_neg $ f i] : has_neg (Π i : I, f i) := 
⟨λ x, λ i, -(x i)⟩


instance add_group [∀ i, add_group $ f i] : add_group (Π i : I, f i) :=
{ zero_add := assume a, by funext ; exact @add_group.zero_add (f i) _ (a i),
  add_zero := assume a, by funext ; exact @add_group.add_zero (f i) _ (a i),
  add_left_neg := assume a, by funext ; exact @add_group.add_left_neg (f i) _ (a i),
  ..indexed_product.has_zero,
  ..indexed_product.has_neg,
  ..indexed_product.add_semigroup }


instance add_comm_group [∀ i, add_comm_group $ f i] : add_comm_group (Π i : I, f i) :=
{ add_comm := assume a b, by funext ; exact @add_comm_group.add_comm (f i) _ (a i) (b i),
  ..indexed_product.add_group }

instance distrib [∀ i, distrib $ f i] : distrib (Π i : I, f i) :=
{ left_distrib := assume a b c, by funext ; exact @distrib.left_distrib (f i) _ (a i) (b i) (c i),
  right_distrib := assume a b c, by funext ; exact @distrib.right_distrib (f i) _ (a i) (b i) (c i),
  ..indexed_product.has_add,
  ..indexed_product.has_mul }

instance ring [∀ i, ring $ f i] : ring (Π i : I, f i) :=
{ ..indexed_product.distrib,
  ..indexed_product.monoid,
  ..indexed_product.add_comm_group }

instance comm_ring [∀ i, comm_ring $ f i] : comm_ring (Π i : I, f i) :=
{ ..indexed_product.comm_semigroup,
  ..indexed_product.ring }

instance has_scalar {α : Type*} [∀ i, has_scalar α $ f i] : has_scalar α (Π i : I, f i) :=
⟨λ s x, λ i, s • (x i)⟩

instance module {α : Type*} [ring α] [∀ i, module α $ f i] : module α (Π i : I, f i) :=
{ smul_add := assume r x y, by funext ; exact @module.smul_add α (f i) _ _ r (x i) (y i),
  add_smul := assume r s x, by funext ; exact @module.add_smul α (f i) _ _ r s (x i),
  mul_smul := assume r s x, by funext ; exact @module.mul_smul α (f i) _ _ r s (x i),
  one_smul := assume x, by funext ; exact @module.one_smul α (f i) _ _ (x i),
  ..indexed_product.has_scalar }

instance vector_space (α : Type*) [field α] [∀ i, vector_space α $ f i] : vector_space α (Π i : I, f i) :=
{ ..indexed_product.module }
end indexed_product