/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Relativity.Tensors.Color.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathematics.PiTensorProduct
import Mathlib.Algebra.Lie.OfAssociative
import Meta.Informal.Basic
/-!

## Lifting functors.

There is a functor from functors `Discrete C ⥤ Rep k G` to
braided monoidal functors `BraidedFunctor (OverColor C) (Rep k G)`.
We call this functor `lift`. It is a lift in the
sense that it is a section of the forgetful functor
`BraidedFunctor (OverColor C) (Rep k G) ⥤ (Discrete C ⥤ Rep k G)`.

Functors in `Discrete C ⥤ Rep k G` form the basic building blocks of tensor structures.
The fact that they extend to monoidal functors `OverColor C ⥤ Rep k G` allows us to
interact more generally with tensors.

-/

namespace IndexNotation
namespace OverColor

open CategoryTheory
open MonoidalCategory
variable {C k : Type} [CommRing k] {G : Type} [Group G]

namespace Discrete

/-- Takes a homomorphism in `Discrete C` to an isomorphism built on the same objects. -/
def homToIso {c1 c2 : Discrete C} (h : c1 ⟶ c2) : c1 ≅ c2 :=
  Discrete.eqToIso (Discrete.eq_of_hom h)

end Discrete

namespace lift
noncomputable section
variable (F F' : Discrete C ⥤ Rep k G) (η : F ⟶ F')

section toRep
/-!

## To representation

Given an object in `OverColor C` and a functor `F : Discrete C ⥤ Rep k G`,
we get an object of `Rep k G` by taking the tensor product of the representations.

-/

variable (F : Discrete C ⥤ Rep k G)

/-- Given an object `f : OverColor C` and a function `F : Discrete C ⥤ Rep k G`, the object
  in `Rep k G` obtained by taking the tensor product of all colors in `f`. -/
def toRep (f : OverColor C) : Rep k G := Rep.of {
  toFun := fun M => PiTensorProduct.map (ι := f.left) (fun x =>
    (F.obj (Discrete.mk (f.hom x))).ρ M),
  map_one' := by
    simp only [map_one, PiTensorProduct.map_one]
  map_mul' := fun M N => by
    simp only [map_mul]
    ext x : 2
    simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, Module.End.mul_apply]}

lemma toRep_ρ (f : OverColor C) (M : G) : (toRep F f).ρ M =
    PiTensorProduct.map (fun x => (F.obj (Discrete.mk (f.hom x))).ρ M) := rfl

lemma toRep_ρ_tprod (f : OverColor C) (M : G) (x : (i : f.left) → F.obj (Discrete.mk (f.hom i))) :
    (toRep F f).ρ M (PiTensorProduct.tprod k x) =
    PiTensorProduct.tprod k fun i => (F.obj (Discrete.mk (f.hom i))).ρ M (x i) := by
  rw [toRep_ρ]
  change (PiTensorProduct.map fun x => _) ((PiTensorProduct.tprod k) x) =_
  rw [PiTensorProduct.map_tprod]
  rfl

lemma toRep_ρ_empty (g : G) : (toRep F (𝟙_ (OverColor C))).ρ g = LinearMap.id := by
    rw [toRep_ρ]
    ext x
    refine PiTensorProduct.induction_on' x (fun r x => ?_) <| fun x y hx hy => by
      rw [map_add, hx, hy]
      rfl
    rw [PiTensorProduct.tprodCoeff_eq_smul_tprod]
    change (PiTensorProduct.map fun x => (F.obj { as := (𝟙_ (OverColor C)).hom x }).ρ g)
        (r • PiTensorProduct.tprod k x) = r • PiTensorProduct.tprod k x
    rw [map_smul]
    congr 1
    rw [PiTensorProduct.map_tprod]
    exact congrArg (PiTensorProduct.tprod k) (funext fun i => Empty.elim i)

lemma toRep_ρ_from_fin0 (c : Fin 0 → C) (g : G) :
    (toRep F (OverColor.mk c)).ρ g = LinearMap.id := by
    rw [toRep_ρ]
    ext x
    refine PiTensorProduct.induction_on' x (fun r x => ?_) <| fun x y hx hy => by
      rw [map_add, hx, hy]
      rfl
    rw [PiTensorProduct.tprodCoeff_eq_smul_tprod]
    change (PiTensorProduct.map fun x => (F.obj { as := (mk c).hom x }).ρ g)
        (r • PiTensorProduct.tprod k x) = r • PiTensorProduct.tprod k x
    rw [map_smul]
    congr 1
    rw [PiTensorProduct.map_tprod]
    exact congrArg (PiTensorProduct.tprod k) (funext fun i => Fin.elim0 i)

open TensorProduct in

lemma toRep_V_carrier (f : OverColor C) :
    (toRep F f).V = ⨂[k] (i : f.left), F.obj (Discrete.mk (f.hom i)) := rfl

end toRep

section homToRepHom
/-!

## Hom to representation hom

Given a morphism in `OverColor C`, `m : f ⟶ g` and a functor `F : Discrete C ⥤ Rep k G`,
we get an morphism in `Rep k G` between `toRep F f` and `toRep F g` by taking the
tensor product.

-/

/-- For a function `F : Discrete C ⥤ Rep k G`, the linear equivalence
  `(F.obj c1).V ≃ₗ[k] (F.obj c2).V` induced by an equality of `c1` and `c2`. -/
def linearIsoOfEq {c1 c2 : Discrete C} (h : c1.as = c2.as) :
    (F.obj c1).V ≃ₗ[k] (F.obj c2).V := LinearEquiv.ofLinear
  (F.mapIso (Discrete.eqToIso h)).hom.hom.toLinearMap
  (F.mapIso (Discrete.eqToIso h)).inv.hom.toLinearMap
  (by
    ext x
    change ((F.mapIso (Discrete.eqToIso h)).inv ≫
      (F.mapIso (Discrete.eqToIso h)).hom).hom x = x
    rw [Iso.inv_hom_id]
    exact Rep.id_apply (A := F.obj c2) x)
  (by
    ext x
    change ((F.mapIso (Discrete.eqToIso h)).hom ≫
      (F.mapIso (Discrete.eqToIso h)).inv).hom x = x
    rw [Iso.hom_inv_id]
    exact Rep.id_apply (A := F.obj c1) x)

lemma linearIsoOfEq_self {c : Discrete C} (h : c.as = c.as) (x : F.obj c) :
    linearIsoOfEq F h x = x := by
  have h' : h = rfl := Subsingleton.elim _ _
  subst h'
  simp [linearIsoOfEq]

lemma linearIsoOfEq_comm_ρ {c1 c2 : Discrete C} (h : c1.as = c2.as) (M : G)
    (x : F.obj c1) : linearIsoOfEq F h ((F.obj c1).ρ M x) =
    (F.obj c2).ρ M (linearIsoOfEq F h x) := by
  have h1 := Discrete.ext_iff.mpr h
  subst h1
  simp only [linearIsoOfEq, eqToIso_refl, Functor.mapIso_refl, Iso.refl_hom,
    Iso.refl_inv, LinearEquiv.ofLinear_apply]
  rfl

/-- Given a morphism in `OverColor C`, `m : f ⟶ g` and a functor `F : Discrete C ⥤ Rep k G`,
  the linear equivalence `(toRep F f).V ≃ₗ[k] (toRep F g).V` formed by reindexing. -/
def linearIsoOfHom {f g : OverColor C} (m : f ⟶ g) : (toRep F f).V ≃ₗ[k] (toRep F g).V :=
  (PiTensorProduct.reindex k (fun x => (F.obj (Discrete.mk (f.hom x))))
    (OverColor.Hom.toEquiv m)).trans
  (PiTensorProduct.congr (fun i =>
    linearIsoOfEq F (Hom.toEquiv_symm_apply m i)))

lemma linearIsoOfHom_tprod {f g : OverColor C} (m : f ⟶ g)
    (x : (i : f.left) → (F.obj (Discrete.mk (f.hom i)))) :
    linearIsoOfHom F m (PiTensorProduct.tprod k x) =
    PiTensorProduct.tprod k (fun i => (linearIsoOfEq F (Hom.toEquiv_symm_apply m i))
    (x ((OverColor.Hom.toEquiv m).symm i))) := by
  rw [linearIsoOfHom]
  simp only [CategoryTheory.Functor.id_obj]
  change (PiTensorProduct.congr fun i => _) ((PiTensorProduct.reindex k
    (fun x => ↑(F.obj (Discrete.mk (f.hom x))).V) (OverColor.Hom.toEquiv m))
    ((PiTensorProduct.tprod k) x)) = _
  rw [PiTensorProduct.reindex_tprod, PiTensorProduct.congr_tprod]
  rfl

/-- Given a morphism in `OverColor C`, `m : f ⟶ g` and a functor `F : Discrete C ⥤ Rep k G`,
  the morphism `(toRep F f) ⟶ (toRep F g)` formed by reindexing. -/
def homToRepHom {f g : OverColor C} (m : f ⟶ g) : toRep F f ⟶ toRep F g :=
  Rep.ofHom {
  toLinearMap := (linearIsoOfHom F m).toLinearMap
  isIntertwining' M := by
    refine LinearMap.ext fun x => ?_
    refine PiTensorProduct.induction_on' x ?_ (by
      intro x y hx hy
      simp only [map_add, hx, hy])
    intro r x
    simp only [PiTensorProduct.tprodCoeff_eq_smul_tprod, map_smul]
    apply congrArg
    change (linearIsoOfHom F m) (((toRep F f).ρ M) ((PiTensorProduct.tprod k) x)) =
      ((toRep F g).ρ M) ((linearIsoOfHom F m) ((PiTensorProduct.tprod k) x))
    rw [toRep_ρ_tprod]
    change (linearIsoOfHom F m) (PiTensorProduct.tprod k
      (fun i => ((F.obj { as := f.hom i }).ρ M) (x i))) =
      ((toRep F g).ρ M) ((linearIsoOfHom F m) ((PiTensorProduct.tprod k) x))
    rw [linearIsoOfHom_tprod F m
      (fun i => ((F.obj { as := f.hom i }).ρ M) (x i))]
    rw [linearIsoOfHom_tprod F m]
    rw [toRep_ρ_tprod]
    apply congrArg
    funext i
    rw [linearIsoOfEq_comm_ρ]
  }

lemma homToRepHom_tprod {X Y : OverColor C} (p : (i : X.left) → F.obj (Discrete.mk (X.hom i)))
    (f : X ⟶ Y) : (homToRepHom F f).hom (PiTensorProduct.tprod k p) =
    PiTensorProduct.tprod k fun (i : Y.left) => linearIsoOfEq F
    (OverColor.Hom.toEquiv_comp_inv_apply f i) (p ((OverColor.Hom.toEquiv f).symm i)) := by
  simp only [homToRepHom, linearIsoOfHom, Functor.id_obj]
  erw [LinearEquiv.trans_apply]
  change (PiTensorProduct.congr fun i => linearIsoOfEq F _)
    ((PiTensorProduct.reindex k (fun x => _) (OverColor.Hom.toEquiv f))
      ((PiTensorProduct.tprod k) p)) = _
  rw [PiTensorProduct.reindex_tprod]
  exact PiTensorProduct.congr_tprod
    (fun i => linearIsoOfEq F (Hom.toEquiv_symm_apply f i))
    fun i => p ((Hom.toEquiv f).symm i)

lemma homToRepHom_id (X : OverColor C) : homToRepHom F (𝟙 X) = 𝟙 _ := by
  ext x
  refine PiTensorProduct.induction_on' x (fun r x => ?_) (fun x y hx hy => by
    calc
      (homToRepHom F (𝟙 X)).hom.toLinearMap (x + y) =
          (homToRepHom F (𝟙 X)).hom.toLinearMap x +
          (homToRepHom F (𝟙 X)).hom.toLinearMap y := LinearMap.map_add _ _ _
      _ = (𝟙 (toRep F X) : toRep F X ⟶ toRep F X).hom.toLinearMap x +
          (𝟙 (toRep F X) : toRep F X ⟶ toRep F X).hom.toLinearMap y :=
        congrArg₂ (fun a b => a + b) hx hy
      _ = (𝟙 (toRep F X) : toRep F X ⟶ toRep F X).hom.toLinearMap (x + y) :=
        (LinearMap.map_add _ _ _).symm)
  rw [PiTensorProduct.tprodCoeff_eq_smul_tprod]
  calc
    (homToRepHom F (𝟙 X)).hom.toLinearMap (r • PiTensorProduct.tprod k x) =
        r • (homToRepHom F (𝟙 X)).hom.toLinearMap (PiTensorProduct.tprod k x) :=
      LinearMap.map_smul _ _ _
    _ = r • (𝟙 (toRep F X) : toRep F X ⟶ toRep F X).hom.toLinearMap
        (PiTensorProduct.tprod k x) := by
      congr 1
      change (homToRepHom F (𝟙 X)).hom (PiTensorProduct.tprod k x) =
        (𝟙 (toRep F X) : toRep F X ⟶ toRep F X).hom (PiTensorProduct.tprod k x)
      rw [homToRepHom_tprod]
      change PiTensorProduct.tprod k (fun i =>
          linearIsoOfEq F (Hom.toEquiv_symm_apply (𝟙 X) i)
            (x ((Hom.toEquiv (𝟙 X)).symm i))) = PiTensorProduct.tprod k x
      apply congrArg (PiTensorProduct.tprod k)
      funext i
      simpa [OverColor.Hom.toEquiv_id] using
        linearIsoOfEq_self F (Hom.toEquiv_symm_apply (𝟙 X) i) (x i)
    _ = (𝟙 (toRep F X) : toRep F X ⟶ toRep F X).hom.toLinearMap
        (r • PiTensorProduct.tprod k x) := (LinearMap.map_smul _ _ _).symm

lemma homToRepHom_comp {X Y Z : OverColor C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    homToRepHom F (f ≫ g) = homToRepHom F f ≫ homToRepHom F g := by
  ext x
  refine PiTensorProduct.induction_on' x (fun r x => ?_) (fun x y hx hy => by
    change (homToRepHom F (f ≫ g)).hom (x + y) = (homToRepHom F f ≫ homToRepHom F g).hom (x + y)
    change (homToRepHom F (f ≫ g)).hom x = (homToRepHom F f ≫ homToRepHom F g).hom x at hx
    change (homToRepHom F (f ≫ g)).hom y = (homToRepHom F f ≫ homToRepHom F g).hom y at hy
    change (homToRepHom F (f ≫ g)).hom.toLinearMap (x + y) =
      (homToRepHom F f ≫ homToRepHom F g).hom.toLinearMap (x + y)
    change (homToRepHom F (f ≫ g)).hom.toLinearMap x =
      (homToRepHom F f ≫ homToRepHom F g).hom.toLinearMap x at hx
    change (homToRepHom F (f ≫ g)).hom.toLinearMap y =
      (homToRepHom F f ≫ homToRepHom F g).hom.toLinearMap y at hy
    calc
      (homToRepHom F (f ≫ g)).hom.toLinearMap (x + y) =
          (homToRepHom F (f ≫ g)).hom.toLinearMap x +
          (homToRepHom F (f ≫ g)).hom.toLinearMap y := LinearMap.map_add _ _ _
      _ = (homToRepHom F f ≫ homToRepHom F g).hom.toLinearMap x +
          (homToRepHom F f ≫ homToRepHom F g).hom.toLinearMap y :=
        congrArg₂ (fun a b => a + b) hx hy
      _ = (homToRepHom F f ≫ homToRepHom F g).hom.toLinearMap (x + y) :=
        (LinearMap.map_add _ _ _).symm)
  rw [PiTensorProduct.tprodCoeff_eq_smul_tprod]
  change (homToRepHom F (f ≫ g)).hom (r • (PiTensorProduct.tprod k) x) =
    (homToRepHom F f ≫ homToRepHom F g).hom (r • (PiTensorProduct.tprod k) x)
  change (homToRepHom F (f ≫ g)).hom.toLinearMap (r • (PiTensorProduct.tprod k) x) =
    (homToRepHom F f ≫ homToRepHom F g).hom.toLinearMap (r • (PiTensorProduct.tprod k) x)
  calc
    (homToRepHom F (f ≫ g)).hom.toLinearMap (r • (PiTensorProduct.tprod k) x) =
        r • (homToRepHom F (f ≫ g)).hom.toLinearMap ((PiTensorProduct.tprod k) x) :=
          LinearMap.map_smul _ _ _
    _ = r • (homToRepHom F f ≫ homToRepHom F g).hom.toLinearMap ((PiTensorProduct.tprod k) x) := by
      apply congrArg (fun z => r • z)
      change (linearIsoOfHom F (CategoryTheory.CategoryStruct.comp f g))
        ((PiTensorProduct.tprod k) x) =
        (linearIsoOfHom F g) ((linearIsoOfHom F f) ((PiTensorProduct.tprod k) x))
      rw [linearIsoOfHom_tprod, linearIsoOfHom_tprod]
      conv_rhs =>
        erw [linearIsoOfHom_tprod F g]
      refine congrArg _ (funext (fun i => ?_))
      simp only [linearIsoOfEq, Functor.mapIso_hom, eqToIso.hom, Functor.mapIso_inv,
        eqToIso.inv, LinearEquiv.ofLinear_apply]
      have hX {c1 c2 c3 : Discrete C} (h1 : c1 = c2) (h2 : c2 = c3)
        (v : F.obj c1) : (F.map (eqToHom h2)).hom.toLinearMap
          ((F.map (eqToHom h1)).hom.toLinearMap v)
        = (F.map (eqToHom (h1.trans h2))).hom.toLinearMap v := by
        subst h2 h1
        simp
      rw [hX]
      rfl
    _ = (homToRepHom F f ≫ homToRepHom F g).hom.toLinearMap
        (r • (PiTensorProduct.tprod k) x) := (LinearMap.map_smul _ _ _).symm

end homToRepHom

/-!

## toRepFunc

The functions `toRep F` and `homToRepHom F` together form a functor.

-/

/-- The `Functor (OverColor C) (Rep k G)` from a functor `Discrete C ⥤ Rep k G`. -/
def toRepFunc : Functor (OverColor C) (Rep k G) where
  obj := toRep F
  map := homToRepHom F
  map_comp := homToRepHom_comp F
  map_id := homToRepHom_id F

/-!

## The braiding of toRepFunc

The functor `toRepFunc` is a braided monoidal functor.
This is made manifest in the result
- `toRepFunc_braidedFunctor`.

-/

/-- The unit isomorphism between `𝟙_ (Rep k G)` and `toRep F (𝟙_ (OverColor C))`
  generated using `PiTensorProduct.isEmptyEquiv`. -/
def toRepUnitIso : 𝟙_ (Rep k G) ≅ toRep F (𝟙_ (OverColor C)) :=
  Rep.mkIso <| Representation.Equiv.mk (PiTensorProduct.isEmptyEquiv Empty).symm (by
    intro g
    apply LinearMap.ext
    intro x
    change (PiTensorProduct.isEmptyEquiv Empty).symm (x) =
      (toRep F (𝟙_ (OverColor C))).ρ g ((PiTensorProduct.isEmptyEquiv Empty).symm x)
    simp only [toRep_ρ_empty F g,
      PiTensorProduct.isEmptyEquiv_symm_apply, LinearMap.id_coe, id_eq]
    )

/-- An equivalence used in the lemma of `μ_tmul_tprod_mk`. Identical to `μModEquiv`
  except with arguments based on maps instead of elements of `OverColor C`. -/
def discreteSumEquiv {X Y : Type} {cX : X → C} {cY : Y → C} (i : X ⊕ Y) :
    Sum.elim (fun i => F.obj (Discrete.mk (cX i)))
    (fun i => F.obj (Discrete.mk (cY i))) i ≃ₗ[k] F.obj (Discrete.mk ((Sum.elim cX cY) i)) :=
  match i with
  | Sum.inl _ => LinearEquiv.refl _ _
  | Sum.inr _ => LinearEquiv.refl _ _

open TensorProduct in
/-- The equivalence of modules corresponding to the tensor. -/
def μModEquiv (X Y : OverColor C) :
    ((toRep F X).V ⊗[k] (toRep F Y).V) ≃ₗ[k] toRep F (X ⊗ Y) :=
  PhysLean.PiTensorProduct.tmulEquiv ≪≫ₗ PiTensorProduct.congr (discreteSumEquiv F)

lemma μModEquiv_tmul_tprod {X Y : OverColor C}
    (p : (i : X.left) → F.obj (Discrete.mk (X.hom i)))
    (q : (i : Y.left) → F.obj (Discrete.mk (Y.hom i))) :
    μModEquiv F X Y (PiTensorProduct.tprod k p ⊗ₜ[k] PiTensorProduct.tprod k q) =
    PiTensorProduct.tprod k fun i =>
    (discreteSumEquiv F i) (PhysLean.PiTensorProduct.elimPureTensor p q i) := by
  rw [μModEquiv]
  simp only [toRep_V_carrier]
  change (PiTensorProduct.congr (discreteSumEquiv F))
      (PhysLean.PiTensorProduct.tmulEquiv
        (PiTensorProduct.tprod k p ⊗ₜ[k] PiTensorProduct.tprod k q)) = _
  rw [PhysLean.PiTensorProduct.tmulEquiv_tmul_tprod]
  rw [PiTensorProduct.congr_tprod]

/-- The natural isomorphism corresponding to the tensor. -/
def μ (X Y : OverColor C) : toRep F X ⊗ toRep F Y ≅ toRep F (X ⊗ Y) :=
  Rep.mkIso <| Representation.Equiv.mk (μModEquiv F X Y)
  (fun M => by
    refine PhysLean.PiTensorProduct.induction_tmul (fun p q => ?_)
    change (μModEquiv F X Y)
      ((toRep F X).ρ M (PiTensorProduct.tprod k p) ⊗ₜ[k]
      (toRep F Y).ρ M (PiTensorProduct.tprod k q)) = (toRep F (X ⊗ Y)).ρ M
      (μModEquiv F X Y (PiTensorProduct.tprod k p ⊗ₜ[k] PiTensorProduct.tprod k q))
    rw [toRep_ρ_tprod, toRep_ρ_tprod]
    erw [μModEquiv_tmul_tprod F
        (fun i => ((F.obj { as := X.hom i }).ρ M) (p i))
        (fun i => ((F.obj { as := Y.hom i }).ρ M) (q i))]
    rw [μModEquiv_tmul_tprod]
    rw [toRep_ρ]
    change _ = (PiTensorProduct.map fun i => (F.obj { as := (X ⊗ Y).hom i }).ρ M)
      ((PiTensorProduct.tprod k) fun i =>
        (discreteSumEquiv F i) (PhysLean.PiTensorProduct.elimPureTensor p q i))
    rw [PiTensorProduct.map_tprod]
    apply congrArg
    funext i
    match i with
    | Sum.inl i =>
      rfl
    | Sum.inr i =>
      rfl)

lemma μ_tmul_tprod {X Y : OverColor C} (p : (i : X.left) → F.obj (Discrete.mk <| X.hom i))
    (q : (i : Y.left) → (F.obj <| Discrete.mk (Y.hom i))) :
    (μ F X Y).hom.hom (PiTensorProduct.tprod k p ⊗ₜ[k] PiTensorProduct.tprod k q) =
    (PiTensorProduct.tprod k) fun i =>
    discreteSumEquiv F i (PhysLean.PiTensorProduct.elimPureTensor p q i) := by
  change μModEquiv F X Y (PiTensorProduct.tprod k p ⊗ₜ[k] PiTensorProduct.tprod k q) =
    (PiTensorProduct.tprod k) fun i =>
    discreteSumEquiv F i (PhysLean.PiTensorProduct.elimPureTensor p q i)
  exact μModEquiv_tmul_tprod F p q

lemma μ_tmul_tprod_mk {X Y : Type} {cX : X → C} {cY : Y → C}
    (p : (i : X) → F.obj (Discrete.mk <| cX i))
    (q : (i : Y) → (F.obj <| Discrete.mk (cY i))) :
    (μ F (OverColor.mk cX) (OverColor.mk cY)).hom.hom
    (PiTensorProduct.tprod k p ⊗ₜ[k] PiTensorProduct.tprod k q)
    = (PiTensorProduct.tprod k) fun i =>
    discreteSumEquiv F i (PhysLean.PiTensorProduct.elimPureTensor p q i) := by
  change μModEquiv F (OverColor.mk cX) (OverColor.mk cY)
    (PiTensorProduct.tprod k p ⊗ₜ[k] PiTensorProduct.tprod k q)
    = (PiTensorProduct.tprod k) fun i =>
    discreteSumEquiv F i (PhysLean.PiTensorProduct.elimPureTensor p q i)
  exact μModEquiv_tmul_tprod F _ _

lemma μ_natural_left {X Y : OverColor C} (f : X ⟶ Y) (Z : OverColor C) :
    MonoidalCategory.whiskerRight (homToRepHom F f) (toRep F Z) ≫ (μ F Y Z).hom =
    (μ F X Z).hom ≫ homToRepHom F (MonoidalCategory.whiskerRight f Z) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine PhysLean.PiTensorProduct.induction_tmul (fun p q => ?_)
  simp only [toRep_V_carrier, tensorObj_of_left, tensorObj_of_hom, CategoryStruct.comp]
  change _ = (homToRepHom F (MonoidalCategory.whiskerRight f Z)).hom
    ((μ F X Z).hom.hom ((PiTensorProduct.tprod k) p ⊗ₜ[k] (PiTensorProduct.tprod k) q))
  rw [μ_tmul_tprod (F := F) (X := X) (Y := Z)]
  change _ = (homToRepHom F (f ▷ Z)).hom
    (PiTensorProduct.tprod k fun i => discreteSumEquiv F i
    (PhysLean.PiTensorProduct.elimPureTensor p q i))
  change (μ F Y Z).hom.hom.toLinearMap
    (((homToRepHom F f).hom (PiTensorProduct.tprod k p)) ⊗ₜ[k]
      (PiTensorProduct.tprod k q)) =
    (homToRepHom F (f ▷ Z)).hom
      (PiTensorProduct.tprod k fun i => discreteSumEquiv F i
      (PhysLean.PiTensorProduct.elimPureTensor p q i))
  have hp : (homToRepHom F f).hom (PiTensorProduct.tprod k p) =
      PiTensorProduct.tprod k fun i => (linearIsoOfEq F _)
        (p ((OverColor.Hom.toEquiv f).symm i)) := homToRepHom_tprod F p f
  rw [hp]
  simp only [toRep_V_carrier, Functor.id_obj]
  change (μ F Y Z).hom.hom.toLinearMap
      (((PiTensorProduct.tprod k) fun i => (linearIsoOfEq F _)
        (p ((OverColor.Hom.toEquiv f).symm i))) ⊗ₜ[k] (PiTensorProduct.tprod k q)) =
    (homToRepHom F (f ▷ Z)).hom
      (PiTensorProduct.tprod k fun i => discreteSumEquiv F i
      (PhysLean.PiTensorProduct.elimPureTensor p q i))
  have hq := homToRepHom_tprod F
    (fun i => discreteSumEquiv F i (PhysLean.PiTensorProduct.elimPureTensor p q i)) (f ▷ Z)
  rw [hq]
  change (μ F Y Z).hom.hom (((PiTensorProduct.tprod k) fun i => (linearIsoOfEq F _)
    (p ((OverColor.Hom.toEquiv f).symm i))) ⊗ₜ[k] (PiTensorProduct.tprod k) q) = _
  rw [μ_tmul_tprod (F := F) (X := Y) (Y := Z)]
  apply congrArg
  funext i
  match i with
  | Sum.inl i => rfl
  | Sum.inr i =>
    simpa [discreteSumEquiv, PhysLean.PiTensorProduct.elimPureTensor] using
      (linearIsoOfEq_self F _ (q i)).symm

lemma μ_natural_right {X Y : OverColor C} (X' : OverColor C) (f : X ⟶ Y) :
    MonoidalCategory.whiskerLeft (toRep F X') (homToRepHom F f) ≫ (μ F X' Y).hom =
    (μ F X' X).hom ≫ homToRepHom F (MonoidalCategory.whiskerLeft X' f) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine PhysLean.PiTensorProduct.induction_tmul (fun p q => ?_)
  simp only [toRep_V_carrier, CategoryStruct.comp]
  change _ = (homToRepHom F (X' ◁ f)).hom ((μ F X' X).hom.hom
    ((PiTensorProduct.tprod k) p ⊗ₜ[k] (PiTensorProduct.tprod k) q))
  rw [μ_tmul_tprod (F := F) (X := X') (Y := X)]
  change _ = (homToRepHom F (X' ◁ f)).hom ((PiTensorProduct.tprod k) fun i =>
    (discreteSumEquiv F i) (PhysLean.PiTensorProduct.elimPureTensor p q i))
  rw [homToRepHom_tprod]
  change (μ F X' Y).hom.hom.toLinearMap
      ((PiTensorProduct.tprod k p) ⊗ₜ[k]
        ((homToRepHom F f).hom (PiTensorProduct.tprod k q))) = _
  have hq : (homToRepHom F f).hom (PiTensorProduct.tprod k q) =
      PiTensorProduct.tprod k fun i => (linearIsoOfEq F _)
        (q ((OverColor.Hom.toEquiv f).symm i)) := homToRepHom_tprod F q f
  rw [hq]
  change (μ F X' Y).hom.hom ((PiTensorProduct.tprod k) p ⊗ₜ[k] (PiTensorProduct.tprod k) fun i =>
    (linearIsoOfEq F _) (q ((OverColor.Hom.toEquiv f).symm i))) = _
  rw [μ_tmul_tprod (F := F) (X := X') (Y := Y)]
  apply congrArg
  funext i
  match i with
  | Sum.inl i =>
    simpa [discreteSumEquiv, PhysLean.PiTensorProduct.elimPureTensor] using
      (linearIsoOfEq_self F _ (p i)).symm
  | Sum.inr i => rfl

lemma associativity (X Y Z : OverColor C) :
    whiskerRight (μ F X Y).hom (toRep F Z) ≫
    (μ F (X ⊗ Y) Z).hom ≫ homToRepHom F (associator X Y Z).hom =
    (associator (toRep F X) (toRep F Y) (toRep F Z)).hom ≫
    whiskerLeft (toRep F X) (μ F Y Z).hom ≫ (μ F X (Y ⊗ Z)).hom := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine PhysLean.PiTensorProduct.induction_assoc' (fun p q m => ?_)
  simp only [toRep_V_carrier, CategoryStruct.comp]
  change (homToRepHom F (α_ X Y Z).hom).hom ((μ F (X ⊗ Y) Z).hom.hom
    ((((μ F X Y).hom.hom ((PiTensorProduct.tprod k) p ⊗ₜ[k]
    (PiTensorProduct.tprod k) q)) ⊗ₜ[k] (PiTensorProduct.tprod k) m))) =
    (μ F X (Y ⊗ Z)).hom.hom ((((PiTensorProduct.tprod k) p ⊗ₜ[k] ((μ F Y Z).hom.hom
    ((PiTensorProduct.tprod k) q ⊗ₜ[k] (PiTensorProduct.tprod k) m)))))
  rw [μ_tmul_tprod, μ_tmul_tprod]
  change (homToRepHom F (α_ X Y Z).hom).hom ((μ F (X ⊗ Y) Z).hom.hom
    (((PiTensorProduct.tprod k) fun i => (discreteSumEquiv F i)
    (PhysLean.PiTensorProduct.elimPureTensor p q i)) ⊗ₜ[k] (PiTensorProduct.tprod k) m)) =
    (μ F X (Y ⊗ Z)).hom.hom ((PiTensorProduct.tprod k) p ⊗ₜ[k] (PiTensorProduct.tprod k) fun i =>
    (discreteSumEquiv F i) (PhysLean.PiTensorProduct.elimPureTensor q m i))
  rw [μ_tmul_tprod, μ_tmul_tprod]
  erw [homToRepHom_tprod]
  apply congrArg
  funext i
  match i with
  | Sum.inl i =>
    simpa [discreteSumEquiv, PhysLean.PiTensorProduct.elimPureTensor] using
      linearIsoOfEq_self F _ (p i)
  | Sum.inr (Sum.inl i) =>
    simpa [discreteSumEquiv, PhysLean.PiTensorProduct.elimPureTensor] using
      linearIsoOfEq_self F _ (q i)
  | Sum.inr (Sum.inr i) =>
    simpa [discreteSumEquiv, PhysLean.PiTensorProduct.elimPureTensor] using
      linearIsoOfEq_self F _ (m i)

open TensorProduct in
lemma left_unitality (X : OverColor C) : (leftUnitor (toRep F X)).hom =
    whiskerRight (toRepUnitIso F).hom (toRep F X) ≫
    (μ F (𝟙_ (OverColor C)) X).hom ≫ homToRepHom F (leftUnitor X).hom := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply PhysLean.PiTensorProduct.induction_mod_tmul (fun x q => ?_)
  haveI : IsEmpty (𝟙_ (OverColor C)).left := by
    change IsEmpty Empty
    infer_instance
  let r : k := x
  let e : ⨂[k] i : (𝟙_ (OverColor C)).left,
      (F.obj { as := (𝟙_ (OverColor C)).hom i }) := (PiTensorProduct.tprod k) isEmptyElim
  simp only [toRep_V_carrier, CategoryStruct.comp, tensorObj_of_left, tensorUnit_of_left,
    tensorObj_of_hom]
  change TensorProduct.lid k (toRep F X) (x ⊗ₜ[k] (PiTensorProduct.tprod k) q) =
    (homToRepHom F (λ_ X).hom).hom ((μ F (𝟙_ (OverColor C)) X).hom.hom
    ((((PiTensorProduct.isEmptyEquiv Empty).symm x) ⊗ₜ[k] (PiTensorProduct.tprod k) q)))
  rw [lid_tmul]
  change r • PiTensorProduct.tprod k q =
    (homToRepHom F (λ_ X).hom).hom ((μ F (𝟙_ (OverColor C)) X).hom.hom
    ((((PiTensorProduct.isEmptyEquiv Empty).symm r) ⊗ₜ[k] (PiTensorProduct.tprod k) q)))
  rw [PiTensorProduct.isEmptyEquiv_symm_apply]
  change r • PiTensorProduct.tprod k q =
    (homToRepHom F (λ_ X).hom).hom ((μ F (𝟙_ (OverColor C)) X).hom.hom
    (((r • e) ⊗ₜ[k] (PiTensorProduct.tprod k) q)))
  let z := e ⊗ₜ[k] (PiTensorProduct.tprod k) q
  have hscalar :
      ((r • e) ⊗ₜ[k] (PiTensorProduct.tprod k) q) =
        r • z :=
    (TensorProduct.smul_tmul' (R := k) (R' := k) r
      e ((PiTensorProduct.tprod k) q)).symm
  erw [hscalar]
  change r • PiTensorProduct.tprod k q =
    (homToRepHom F (λ_ X).hom).hom ((μ F (𝟙_ (OverColor C)) X).hom.hom
    (r • z))
  change r • PiTensorProduct.tprod k q =
    (homToRepHom F (λ_ X).hom).hom.toLinearMap
      ((μ F (𝟙_ (OverColor C)) X).hom.hom.toLinearMap
      (r • z))
  let L := ((homToRepHom F (λ_ X).hom).hom.toLinearMap).comp
    ((μ F (𝟙_ (OverColor C)) X).hom.hom.toLinearMap)
  change r • PiTensorProduct.tprod k q = L (r • z)
  have hmap : L (r • z) = r • L z := L.map_smul r z
  rw [hmap]
  apply congrArg (fun y => r • y)
  dsimp [L]
  dsimp [z]
  dsimp [e]
  conv_rhs =>
    arg 2
    erw [μ_tmul_tprod (F := F) (X := 𝟙_ (OverColor C)) (Y := X)
      (fun i => isEmptyElim i) q]
  erw [homToRepHom_tprod]
  apply congrArg (PiTensorProduct.tprod k)
  funext i
  simpa [PhysLean.PiTensorProduct.elimPureTensor] using
    (linearIsoOfEq_self F _ (q i)).symm

open TensorProduct in
lemma right_unitality (X : OverColor C) : (rightUnitor (toRep F X)).hom =
    whiskerLeft (toRep F X) (toRepUnitIso F).hom ≫
    (μ F X (𝟙_ (OverColor C))).hom ≫ homToRepHom F (rightUnitor X).hom := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply PhysLean.PiTensorProduct.induction_tmul_mod (fun p x => ?_)
  haveI : IsEmpty (𝟙_ (OverColor C)).left := by
    change IsEmpty Empty
    infer_instance
  let r : k := x
  let e : ⨂[k] i : (𝟙_ (OverColor C)).left,
      (F.obj { as := (𝟙_ (OverColor C)).hom i }) := (PiTensorProduct.tprod k) isEmptyElim
  simp only [CategoryStruct.comp]
  change TensorProduct.rid k (toRep F X) ((PiTensorProduct.tprod k) p ⊗ₜ[k] x) =
    (homToRepHom F (ρ_ X).hom).hom ((μ F X (𝟙_ (OverColor C))).hom.hom
    ((((PiTensorProduct.tprod k) p ⊗ₜ[k] ((PiTensorProduct.isEmptyEquiv Empty).symm x)))))
  rw [rid_tmul]
  change r • PiTensorProduct.tprod k p =
    (homToRepHom F (ρ_ X).hom).hom ((μ F X (𝟙_ (OverColor C))).hom.hom
    ((((PiTensorProduct.tprod k) p ⊗ₜ[k] ((PiTensorProduct.isEmptyEquiv Empty).symm r)))))
  rw [PiTensorProduct.isEmptyEquiv_symm_apply]
  change r • PiTensorProduct.tprod k p =
    (homToRepHom F (ρ_ X).hom).hom ((μ F X (𝟙_ (OverColor C))).hom.hom
    (((PiTensorProduct.tprod k) p ⊗ₜ[k] (r • (PiTensorProduct.tprod k) isEmptyElim))))
  change r • PiTensorProduct.tprod k p =
    (homToRepHom F (ρ_ X).hom).hom ((μ F X (𝟙_ (OverColor C))).hom.hom
    (((PiTensorProduct.tprod k) p ⊗ₜ[k] (r • e))))
  let z := (PiTensorProduct.tprod k) p ⊗ₜ[k] e
  have hscalar :
      ((PiTensorProduct.tprod k) p ⊗ₜ[k] (r • e)) =
        r • z :=
    TensorProduct.tmul_smul (R := k) (R' := k) r ((PiTensorProduct.tprod k) p)
      e
  erw [hscalar]
  change r • PiTensorProduct.tprod k p =
    (homToRepHom F (ρ_ X).hom).hom.toLinearMap
      ((μ F X (𝟙_ (OverColor C))).hom.hom.toLinearMap
      (r • z))
  let L := ((homToRepHom F (ρ_ X).hom).hom.toLinearMap).comp
    ((μ F X (𝟙_ (OverColor C))).hom.hom.toLinearMap)
  change r • PiTensorProduct.tprod k p = L (r • z)
  have hmap : L (r • z) = r • L z := L.map_smul r z
  rw [hmap]
  apply congrArg (fun y => r • y)
  dsimp [L]
  dsimp [z]
  dsimp [e]
  conv_rhs =>
    arg 2
    erw [μ_tmul_tprod (F := F) (X := X) (Y := 𝟙_ (OverColor C))
      p (fun i => isEmptyElim i)]
  erw [homToRepHom_tprod]
  apply congrArg (PiTensorProduct.tprod k)
  funext i
  simpa [PhysLean.PiTensorProduct.elimPureTensor] using
    (linearIsoOfEq_self F _ (p i)).symm

lemma braided' (X Y : OverColor C) : (μ F X Y).hom ≫ (homToRepHom F) (β_ X Y).hom =
    (β_ (toRep F X) (toRep F Y)).hom ≫ (μ F Y X).hom := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply PhysLean.PiTensorProduct.induction_tmul (fun p q => ?_)
  simp only [toRep_V_carrier, CategoryStruct.comp]
  change (homToRepHom F (β_ X Y).hom).hom ((μ F X Y).hom.hom
    ((PiTensorProduct.tprod k) p ⊗ₜ[k] (PiTensorProduct.tprod k) q)) = (μ F Y X).hom.hom
    ((PiTensorProduct.tprod k) q ⊗ₜ[k] (PiTensorProduct.tprod k) p)
  rw [μ_tmul_tprod, μ_tmul_tprod]
  erw [homToRepHom_tprod]
  apply congrArg
  funext i
  match i with
  | Sum.inl i =>
    simpa [discreteSumEquiv, PhysLean.PiTensorProduct.elimPureTensor] using
      linearIsoOfEq_self F _ (q i)
  | Sum.inr i =>
    simpa [discreteSumEquiv, PhysLean.PiTensorProduct.elimPureTensor] using
      linearIsoOfEq_self F _ (p i)

lemma braided (X Y : OverColor C) :
    (homToRepHom F) (β_ X Y).hom = (μ F X Y).inv ≫
    ((β_ (toRep F X) (toRep F Y)).hom ≫ (μ F Y X).hom) :=
  (Iso.eq_inv_comp (μ F X Y)).mpr (braided' F X Y)

/-- The lift of a functor is lax braided. -/
instance toRepFunc_laxBraidedFunctor : Functor.LaxBraided (toRepFunc F) where
  ε := (toRepUnitIso F).hom
  μ := fun X Y => (μ F X Y).hom
  μ_natural_left := μ_natural_left F
  μ_natural_right := μ_natural_right F
  associativity := associativity F
  left_unitality := left_unitality F
  right_unitality := right_unitality F
  braided := fun X Y => by
    simp only [toRepFunc]
    rw [braided F X Y]
    simp

/-- The lift of a functor is monoidal. -/
instance toRepFunc_monoidalFunctor : Functor.Monoidal (toRepFunc F) :=
  haveI : IsIso (Functor.LaxMonoidal.ε (toRepFunc F)) := by
    change IsIso (toRepUnitIso F).hom
    infer_instance
  haveI : (∀ (X Y : OverColor C), IsIso (Functor.LaxMonoidal.μ (toRepFunc F) X Y)) := by
    intro X Y
    change IsIso (μ F X Y).hom
    infer_instance
  Functor.Monoidal.ofLaxMonoidal _

/-- The lift of a functor is braided. -/
instance toRepFunc_braidedFunctor : Functor.Braided (toRepFunc F) := Functor.Braided.mk (fun X Y =>
  Functor.LaxBraided.braided X Y)

/-!

## The natural transformation `repNatTransOfColor`

Given two functors `F F' : Discrete C ⥤ Rep k G` and a natural transformation `η : F ⟶ F'`,
we construct a natural transformation `repNatTransOfColor : toRepFunc F ⟶ toRepFunc F'`
by taking the tensor product of the corresponding morphisms in `η`.

-/

variable {F F' : Discrete C ⥤ Rep k G} (η : F ⟶ F')

/-- Given two functors `F F' : Discrete C ⥤ Rep k G` and a natural transformation `η : F ⟶ F'`,
  and an `X : OverColor C`, the `(toRepFunc F).obj X ⟶ (toRepFunc F').obj X` in `Rep k G`
  constructed by the tensor product of the morphisms in `η` with corresponding color. -/
def repNatTransOfColorApp (X : OverColor C) : (toRepFunc F).obj X ⟶ (toRepFunc F').obj X :=
  Rep.ofHom {
  toLinearMap := PiTensorProduct.map (fun x => (η.app (Discrete.mk (X.hom x))).hom.toLinearMap)
  isIntertwining' M := by
    refine LinearMap.ext fun x => ?_
    refine PiTensorProduct.induction_on' x ?_ (by
      intro x y hx hy
      simp only [map_add]
      erw [hx, hy]
      )
    intro r x
    simp only [PiTensorProduct.tprodCoeff_eq_smul_tprod,
      _root_.map_smul]
    apply congrArg
    change (PiTensorProduct.map fun x => (η.app { as := X.hom x }).hom.toLinearMap)
      ((((toRepFunc F).obj X).ρ M) ((PiTensorProduct.tprod k) x)) =
      (((toRepFunc F').obj X).ρ M) ((PiTensorProduct.map fun x =>
      (η.app { as := X.hom x }).hom.toLinearMap) ((PiTensorProduct.tprod k) x))
    rw [PiTensorProduct.map_tprod]
    simp only [Functor.id_obj, toRepFunc]
    change (PiTensorProduct.map fun x => (η.app { as := X.hom x }).hom.toLinearMap)
      (((toRep F X).ρ M) ((PiTensorProduct.tprod k) x)) =
      ((toRep F' X).ρ M) ((PiTensorProduct.tprod k) fun i =>
      (η.app { as := X.hom i }).hom (x i))
    rw [toRep_ρ_tprod, toRep_ρ_tprod]
    erw [PiTensorProduct.map_tprod]
    exact congrArg (PiTensorProduct.tprod k) <| funext fun i => by
      simpa using Rep.hom_comm_apply (η.app (Discrete.mk (X.hom i))) M (x i)
  }

lemma repNatTransOfColorApp_tprod (X : OverColor C)
    (p : (i : X.left) → F.obj (Discrete.mk (X.hom i))) :
    (repNatTransOfColorApp η X).hom (PiTensorProduct.tprod k p) =
    PiTensorProduct.tprod k fun i => (η.app (Discrete.mk (X.hom i))).hom (p i) := by
  simp only [repNatTransOfColorApp]
  erw [PiTensorProduct.map_tprod]
  rfl

lemma repNatTransOfColorApp_naturality {X Y : OverColor C} (f : X ⟶ Y) :
    (toRepFunc F).map f ≫ repNatTransOfColorApp η Y =
    repNatTransOfColorApp η X ≫ (toRepFunc F').map f := by
  ext x
  refine PiTensorProduct.induction_on' x ?_ (by
    intro x y hx hy
    change ((toRepFunc F).map f ≫ repNatTransOfColorApp η Y).hom (x + y) =
      (repNatTransOfColorApp η X ≫ (toRepFunc F').map f).hom (x + y)
    change ((toRepFunc F).map f ≫ repNatTransOfColorApp η Y).hom x =
      (repNatTransOfColorApp η X ≫ (toRepFunc F').map f).hom x at hx
    change ((toRepFunc F).map f ≫ repNatTransOfColorApp η Y).hom y =
      (repNatTransOfColorApp η X ≫ (toRepFunc F').map f).hom y at hy
    change ((toRepFunc F).map f ≫ repNatTransOfColorApp η Y).hom.toLinearMap (x + y) =
      (repNatTransOfColorApp η X ≫ (toRepFunc F').map f).hom.toLinearMap (x + y)
    change ((toRepFunc F).map f ≫ repNatTransOfColorApp η Y).hom.toLinearMap x =
      (repNatTransOfColorApp η X ≫ (toRepFunc F').map f).hom.toLinearMap x at hx
    change ((toRepFunc F).map f ≫ repNatTransOfColorApp η Y).hom.toLinearMap y =
      (repNatTransOfColorApp η X ≫ (toRepFunc F').map f).hom.toLinearMap y at hy
    calc
      ((toRepFunc F).map f ≫ repNatTransOfColorApp η Y).hom.toLinearMap (x + y) =
          ((toRepFunc F).map f ≫ repNatTransOfColorApp η Y).hom.toLinearMap x +
          ((toRepFunc F).map f ≫ repNatTransOfColorApp η Y).hom.toLinearMap y :=
        LinearMap.map_add _ _ _
      _ = (repNatTransOfColorApp η X ≫ (toRepFunc F').map f).hom.toLinearMap x +
          (repNatTransOfColorApp η X ≫ (toRepFunc F').map f).hom.toLinearMap y :=
        congrArg₂ (fun a b => a + b) hx hy
      _ = (repNatTransOfColorApp η X ≫ (toRepFunc F').map f).hom.toLinearMap (x + y) :=
        (LinearMap.map_add _ _ _).symm)
  intro r x
  rw [PiTensorProduct.tprodCoeff_eq_smul_tprod]
  have hpure : ((toRepFunc F).map f ≫ repNatTransOfColorApp η Y).hom.toLinearMap
      ((PiTensorProduct.tprod k) x) =
    (repNatTransOfColorApp η X ≫ (toRepFunc F').map f).hom.toLinearMap
      ((PiTensorProduct.tprod k) x) := by
    change (repNatTransOfColorApp η Y).hom ((homToRepHom F f).hom ((PiTensorProduct.tprod k) x)) =
      (homToRepHom F' f).hom ((repNatTransOfColorApp η X).hom ((PiTensorProduct.tprod k) x))
    rw [repNatTransOfColorApp_tprod, homToRepHom_tprod]
    erw [repNatTransOfColorApp_tprod, homToRepHom_tprod]
    apply congrArg
    funext i
    simp only [linearIsoOfEq, Functor.mapIso_hom, eqToIso.hom, Functor.mapIso_inv,
      eqToIso.inv, LinearEquiv.ofLinear_apply]
    generalize_proofs h1
    have h := congrArg
      (fun m => m.hom.toLinearMap (x ((Hom.toEquiv f).symm i)))
      (η.naturality (eqToHom h1))
    exact h
  change ((toRepFunc F).map f ≫ repNatTransOfColorApp η Y).hom.toLinearMap
      (r • (PiTensorProduct.tprod k) x) =
    (repNatTransOfColorApp η X ≫ (toRepFunc F').map f).hom.toLinearMap
      (r • (PiTensorProduct.tprod k) x)
  exact calc
    ((toRepFunc F).map f ≫ repNatTransOfColorApp η Y).hom.toLinearMap
        (r • (PiTensorProduct.tprod k) x) =
      r • ((toRepFunc F).map f ≫ repNatTransOfColorApp η Y).hom.toLinearMap
        ((PiTensorProduct.tprod k) x) := LinearMap.map_smul _ _ _
    _ = r • (repNatTransOfColorApp η X ≫ (toRepFunc F').map f).hom.toLinearMap
        ((PiTensorProduct.tprod k) x) := congrArg (fun z => r • z) hpure
    _ = (repNatTransOfColorApp η X ≫ (toRepFunc F').map f).hom.toLinearMap
        (r • (PiTensorProduct.tprod k) x) := (LinearMap.map_smul _ _ _).symm
/- old proof
  simp only [toRepFunc, toRep_V_carrier]
  change (repNatTransOfColorApp η Y).hom ((homToRepHom F f).hom ((PiTensorProduct.tprod k) x)) =
  (homToRepHom F' f).hom ((repNatTransOfColorApp η X).hom ((PiTensorProduct.tprod k) x))
  rw [repNatTransOfColorApp_tprod, homToRepHom_tprod]
  erw [repNatTransOfColorApp_tprod, homToRepHom_tprod]
  apply congrArg
  funext i
  simp only [linearIsoOfEq, Functor.mapIso_hom, eqToIso.hom, Functor.mapIso_inv,
    eqToIso.inv, LinearEquiv.ofLinear_apply]
  generalize_proofs h1
  have hn := ModuleCat.hom_ext_iff.mp <| Action.hom_ext_iff.mp <|
    η.naturality (eqToHom h1)
  have h := LinearMap.congr_fun hn (x ((Hom.toEquiv f).symm i))
  simpa
-/

/-- Given a natural transformation between `F F' : Discrete C ⥤ Rep k G` the
  monoidal natural transformation between `toRepFunc F` and `toRepFunc F'`. -/
def repNatTransOfColor (η : F ⟶ F') : (toRepFunc F) ⟶ (toRepFunc F') where
  app X := repNatTransOfColorApp η X
  naturality {_ _} f := repNatTransOfColorApp_naturality η f
/-!

## The Monoidal structure of `repNatTransOfColor`

The natural transformation `repNatTransOfColor` is monoidal,
which is made manifest in the results
- `repNatTransOfColor_isMonoidal`.

-/

lemma repNatTransOfColorApp_unit : Functor.LaxMonoidal.ε (toRepFunc F) ≫
    repNatTransOfColorApp η (𝟙_ (OverColor C)) = Functor.LaxMonoidal.ε (toRepFunc F') := by
  ext
  haveI : IsEmpty (𝟙_ (OverColor C)).left := by
    change IsEmpty Empty
    infer_instance
  change (repNatTransOfColorApp η (𝟙_ (OverColor C))).hom
      ((toRepUnitIso F).hom.hom.toLinearMap 1) =
    (toRepUnitIso F').hom.hom.toLinearMap 1
  change (repNatTransOfColorApp η (𝟙_ (OverColor C))).hom
      ((PiTensorProduct.isEmptyEquiv Empty).symm 1) =
    (PiTensorProduct.isEmptyEquiv Empty).symm 1
  rw [PiTensorProduct.isEmptyEquiv_symm_apply]
  rw [PiTensorProduct.isEmptyEquiv_symm_apply]
  change (repNatTransOfColorApp η (𝟙_ (OverColor C))).hom
      ((1 : k) • (PiTensorProduct.tprod k) isEmptyElim) =
    (1 : k) • (PiTensorProduct.tprod k) isEmptyElim
  change (repNatTransOfColorApp η (𝟙_ (OverColor C))).hom.toLinearMap
      ((1 : k) • (PiTensorProduct.tprod k) isEmptyElim) =
    (1 : k) • (PiTensorProduct.tprod k) isEmptyElim
  have hmap := ((repNatTransOfColorApp η (𝟙_ (OverColor C))).hom.toLinearMap).map_smul
    (1 : k) ((PiTensorProduct.tprod k) isEmptyElim)
  trans (1 : k) • (repNatTransOfColorApp η (𝟙_ (OverColor C))).hom.toLinearMap
      ((PiTensorProduct.tprod k) isEmptyElim)
  · exact hmap
  simp only [one_smul]
  haveI : IsEmpty ((𝟭 Type).obj (𝟙_ (OverColor C)).of.left) := by
    change IsEmpty Empty
    infer_instance
  change (PiTensorProduct.map fun x => (η.app { as := (𝟙_ (OverColor C)).hom x }).hom.toLinearMap)
      ((PiTensorProduct.tprod k) isEmptyElim) =
    (PiTensorProduct.tprod k) isEmptyElim
  rw [PiTensorProduct.map_tprod]
  apply congrArg (PiTensorProduct.tprod k)
  funext i
  exact isEmptyElim i

lemma repNatTransOfColorApp_tensor (X Y : OverColor C) :
    (μ F X Y).hom ≫ repNatTransOfColorApp η (X ⊗ Y) =
    (repNatTransOfColorApp η X ⊗ₘ repNatTransOfColorApp η Y) ≫
    (μ F' X Y).hom := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine PhysLean.PiTensorProduct.induction_tmul (fun p q => ?_)
  change (repNatTransOfColorApp η (X ⊗ Y)).hom
      ((μ F X Y).hom.hom (PiTensorProduct.tprod k p ⊗ₜ[k] PiTensorProduct.tprod k q)) =
    (μ F' X Y).hom.hom
      (((repNatTransOfColorApp η X).hom (PiTensorProduct.tprod k p)) ⊗ₜ[k]
      ((repNatTransOfColorApp η Y).hom (PiTensorProduct.tprod k q)))
  rw [μ_tmul_tprod (F := F) (X := X) (Y := Y)]
  rw [repNatTransOfColorApp_tprod]
  rw [repNatTransOfColorApp_tprod]
  change (repNatTransOfColorApp η (X ⊗ Y)).hom
      ((PiTensorProduct.tprod k) fun i =>
        discreteSumEquiv F i (PhysLean.PiTensorProduct.elimPureTensor p q i)) =
    (μ F' X Y).hom.hom
      (((PiTensorProduct.tprod k) fun i => (η.app { as := X.hom i }).hom (p i)) ⊗ₜ[k]
      ((PiTensorProduct.tprod k) fun i => (η.app { as := Y.hom i }).hom (q i)))
  rw [μ_tmul_tprod (F := F') (X := X) (Y := Y)]
  rw [repNatTransOfColorApp_tprod]
  apply congrArg
  funext i
  match i with
  | Sum.inr i => rfl
  | Sum.inl i => rfl

/-- The lift of a natural transformation is monoidal. -/
instance repNatTransOfColor_isMonoidal : NatTrans.IsMonoidal (repNatTransOfColor η) where
  unit := repNatTransOfColorApp_unit η
  tensor X Y := by
    change (μ F X Y).hom ≫ repNatTransOfColorApp η (X ⊗ Y) =
      (repNatTransOfColorApp η X ⊗ₘ repNatTransOfColorApp η Y) ≫ (μ F' X Y).hom
    exact repNatTransOfColorApp_tensor η X Y

end
end lift
open lift

/-!

## The functor `lift`

-/

/-- The functor taking functors in `Discrete C ⥤ Rep k G` to monoidal functors in
  `BraidedFunctor (OverColor C) (Rep k G)`, built on the PiTensorProduct. -/
noncomputable def lift : (Discrete C ⥤ Rep k G) ⥤ LaxBraidedFunctor (OverColor C) (Rep k G) where
  obj F := LaxBraidedFunctor.of (lift.toRepFunc F)
  map {F F'} η := by
    let f : (LaxBraidedFunctor.of (lift.toRepFunc F)).toFunctor ⟶
        (LaxBraidedFunctor.of (lift.toRepFunc F')).toFunctor := repNatTransOfColor η
    haveI : NatTrans.IsMonoidal f := by
      dsimp [f]
      exact repNatTransOfColor_isMonoidal η
    exact LaxBraidedFunctor.homMk
      (F := LaxBraidedFunctor.of (lift.toRepFunc _))
      (G := LaxBraidedFunctor.of (lift.toRepFunc _))
      f
  map_id F := by
    simp only [repNatTransOfColor]
    refine LaxBraidedFunctor.hom_ext ?_
    ext X : 2
    simp only [LaxBraidedFunctor.toLaxMonoidalFunctor_toFunctor, LaxBraidedFunctor.of_toFunctor,
      LaxBraidedFunctor.homMk_hom_hom, LaxBraidedFunctor.id_hom, NatTrans.id_app]
    ext x
    refine PiTensorProduct.induction_on' x ?_ (by
      intro x y hx hy
      change (repNatTransOfColorApp (𝟙 F) X).hom.toLinearMap (x + y) = x + y
      change (repNatTransOfColorApp (𝟙 F) X).hom.toLinearMap x = x at hx
      change (repNatTransOfColorApp (𝟙 F) X).hom.toLinearMap y = y at hy
      calc
        (repNatTransOfColorApp (𝟙 F) X).hom.toLinearMap (x + y) =
          (repNatTransOfColorApp (𝟙 F) X).hom.toLinearMap x +
            (repNatTransOfColorApp (𝟙 F) X).hom.toLinearMap y := LinearMap.map_add _ _ _
        _ = x + y := congrArg₂ (fun a b => a + b) hx hy)
    intro r y
    rw [PiTensorProduct.tprodCoeff_eq_smul_tprod]
    have hpure : (repNatTransOfColorApp (𝟙 F) X).hom.toLinearMap
        ((PiTensorProduct.tprod k) y) = (PiTensorProduct.tprod k) y := by
      change (repNatTransOfColorApp (𝟙 F) X).hom ((PiTensorProduct.tprod k) y) =
        (PiTensorProduct.tprod k) y
      rw [repNatTransOfColorApp_tprod]
      apply congrArg (PiTensorProduct.tprod k)
      funext i
      rfl
    change (repNatTransOfColorApp (𝟙 F) X).hom.toLinearMap
        (r • (PiTensorProduct.tprod k) y) = r • (PiTensorProduct.tprod k) y
    exact calc
      (repNatTransOfColorApp (𝟙 F) X).hom.toLinearMap
          (r • (PiTensorProduct.tprod k) y) =
        r • (repNatTransOfColorApp (𝟙 F) X).hom.toLinearMap
          ((PiTensorProduct.tprod k) y) := LinearMap.map_smul _ _ _
      _ = r • (PiTensorProduct.tprod k) y := congrArg (fun z => r • z) hpure
  map_comp {F G H} η θ := by
    refine LaxBraidedFunctor.hom_ext ?_
    ext X : 2
    simp only [LaxBraidedFunctor.toLaxMonoidalFunctor_toFunctor, LaxBraidedFunctor.of_toFunctor,
      LaxBraidedFunctor.homMk_hom_hom, LaxBraidedFunctor.comp_hom]
    ext x
    refine PiTensorProduct.induction_on' x ?_ (by
      intro x y hx hy
      change (repNatTransOfColorApp (η ≫ θ) X).hom.toLinearMap (x + y) =
        (repNatTransOfColorApp η X ≫ repNatTransOfColorApp θ X).hom.toLinearMap (x + y)
      change (repNatTransOfColorApp (η ≫ θ) X).hom.toLinearMap x =
        (repNatTransOfColorApp η X ≫ repNatTransOfColorApp θ X).hom.toLinearMap x at hx
      change (repNatTransOfColorApp (η ≫ θ) X).hom.toLinearMap y =
        (repNatTransOfColorApp η X ≫ repNatTransOfColorApp θ X).hom.toLinearMap y at hy
      calc
        (repNatTransOfColorApp (η ≫ θ) X).hom.toLinearMap (x + y) =
          (repNatTransOfColorApp (η ≫ θ) X).hom.toLinearMap x +
            (repNatTransOfColorApp (η ≫ θ) X).hom.toLinearMap y := LinearMap.map_add _ _ _
        _ = (repNatTransOfColorApp η X ≫ repNatTransOfColorApp θ X).hom.toLinearMap x +
            (repNatTransOfColorApp η X ≫ repNatTransOfColorApp θ X).hom.toLinearMap y :=
          congrArg₂ (fun a b => a + b) hx hy
        _ = (repNatTransOfColorApp η X ≫ repNatTransOfColorApp θ X).hom.toLinearMap (x + y) :=
          (LinearMap.map_add _ _ _).symm)
    intro r y
    rw [PiTensorProduct.tprodCoeff_eq_smul_tprod]
    have hpure :
        (repNatTransOfColorApp (η ≫ θ) X).hom.toLinearMap
          ((PiTensorProduct.tprod k) y) =
        (repNatTransOfColorApp η X ≫ repNatTransOfColorApp θ X).hom.toLinearMap
          ((PiTensorProduct.tprod k) y) := by
      erw [repNatTransOfColorApp_tprod]
      change _ = (repNatTransOfColorApp θ X).hom
        ((repNatTransOfColorApp η X).hom ((PiTensorProduct.tprod k) y))
      rw [lift.repNatTransOfColorApp_tprod]
      erw [lift.repNatTransOfColorApp_tprod]
      rfl
    change (repNatTransOfColorApp (η ≫ θ) X).hom.toLinearMap
        (r • (PiTensorProduct.tprod k) y) =
      (repNatTransOfColorApp η X ≫ repNatTransOfColorApp θ X).hom.toLinearMap
        (r • (PiTensorProduct.tprod k) y)
    exact calc
      (repNatTransOfColorApp (η ≫ θ) X).hom.toLinearMap
          (r • (PiTensorProduct.tprod k) y) =
        r • (repNatTransOfColorApp (η ≫ θ) X).hom.toLinearMap
          ((PiTensorProduct.tprod k) y) := LinearMap.map_smul _ _ _
      _ = r • (repNatTransOfColorApp η X ≫ repNatTransOfColorApp θ X).hom.toLinearMap
          ((PiTensorProduct.tprod k) y) := congrArg (fun z => r • z) hpure
      _ = (repNatTransOfColorApp η X ≫ repNatTransOfColorApp θ X).hom.toLinearMap
          (r • (PiTensorProduct.tprod k) y) := (LinearMap.map_smul _ _ _).symm

namespace lift
variable (F F' : Discrete C ⥤ Rep k G) (η : F ⟶ F')

/-- The lift of a functor is monoidal. -/
noncomputable instance : (lift.obj F).Monoidal := toRepFunc_monoidalFunctor F

/-- The lift of a functor is lax-braided. -/
noncomputable instance : (lift.obj F).LaxBraided := toRepFunc_laxBraidedFunctor F

/-- The lift of a functor is braided. -/
noncomputable instance : (lift.obj F).Braided := Functor.Braided.mk (fun X Y =>
  Functor.LaxBraided.braided X Y)

lemma map_tprod (F : Discrete C ⥤ Rep k G) {X Y : OverColor C} (f : X ⟶ Y)
    (p : (i : X.left) → F.obj (Discrete.mk <| X.hom i)) :
    ((lift.obj F).map f).hom (PiTensorProduct.tprod k p) =
    PiTensorProduct.tprod k fun (i : Y.left) => linearIsoOfEq F
    (OverColor.Hom.toEquiv_comp_inv_apply f i) (p ((OverColor.Hom.toEquiv f).symm i)) := by
  simp only [lift, toRepFunc]
  erw [homToRepHom_tprod]

lemma obj_μ_tprod_tmul (F : Discrete C ⥤ Rep k G) (X Y : OverColor C)
    (p : (i : X.left) → (F.obj (Discrete.mk <| X.hom i)))
    (q : (i : Y.left) → F.obj (Discrete.mk <| Y.hom i)) :
    (Functor.LaxMonoidal.μ (lift.obj F).toFunctor X Y).hom
    (PiTensorProduct.tprod k p ⊗ₜ[k] PiTensorProduct.tprod k q) =
    (PiTensorProduct.tprod k) fun i =>
    discreteSumEquiv F i (PhysLean.PiTensorProduct.elimPureTensor p q i) := by
  exact μ_tmul_tprod F p q

lemma μIso_inv_tprod (F : Discrete C ⥤ Rep k G) (X Y : OverColor C)
    (p : (i : (X ⊗ Y).left) → F.obj (Discrete.mk <| (X ⊗ Y).hom i)) :
    (lift.μ F X Y).inv.hom (PiTensorProduct.tprod k p) =
    (PiTensorProduct.tprod k (fun i => p (Sum.inl i))) ⊗ₜ[k]
    (PiTensorProduct.tprod k (fun i => p (Sum.inr i))) := by
  change (μModEquiv F X Y).symm (PiTensorProduct.tprod k p) = _
  rw [← LinearEquiv.eq_symm_apply]
  change (PiTensorProduct.tprod k) p =
    μModEquiv F X Y
      ((PiTensorProduct.tprod k (fun i => p (Sum.inl i))) ⊗ₜ[k]
      (PiTensorProduct.tprod k (fun i => p (Sum.inr i))))
  rw [μModEquiv_tmul_tprod]
  apply congrArg (PiTensorProduct.tprod k)
  funext i
  match i with
  | Sum.inl i => rfl
  | Sum.inr i => rfl

lemma inv_μ (X Y : OverColor C) :
    (lift.μ F X Y).inv =
    (lift.μ F X Y).inv := by
  rfl

end lift

/-!

## The forgetful functor from `BraidedFunctor (OverColor C) (Rep k G)` to `Discrete C ⥤ Rep k G`

-/

/-- The natural inclusion of `Discrete C` into `OverColor C`. -/
def incl : Discrete C ⥤ OverColor C := Discrete.functor fun c =>
  OverColor.mk (fun (_ : Fin 1) => c)

noncomputable section

/-- The forgetful map from `BraidedFunctor (OverColor C) (Rep k G)` to `Discrete C ⥤ Rep k G`
  built on the inclusion `incl` and forgetting the monoidal structure. -/
def forget : LaxBraidedFunctor (OverColor C) (Rep k G) ⥤ (Discrete C ⥤ Rep k G) where
  obj F := Discrete.functor fun c => F.obj (incl.obj (Discrete.mk c))
  map η := Discrete.natTrans fun c => η.hom.hom.app (incl.obj c)

variable (F F' : Discrete C ⥤ Rep k G) (η : F ⟶ F')

open TensorProduct

/--
The `forgetLiftAppV` function takes an object `c` of type `C` and returns a linear equivalence
between the vector space obtained by applying the lift of `F` and that obtained by applying
`F`.
--/
def forgetLiftAppV (c : C) : ((lift.obj F).obj (OverColor.mk (fun (_ : Fin 1) => c))).V ≃ₗ[k]
    (F.obj (Discrete.mk c)).V :=
  (PiTensorProduct.subsingletonEquiv 0 :
    (⨂[k] (_ : Fin 1), (F.obj (Discrete.mk c))) ≃ₗ[k] F.obj (Discrete.mk c))

@[simp]
lemma forgetLiftAppV_symm_apply (c : C) (x : (F.obj (Discrete.mk c)).V) :
    (forgetLiftAppV F c).symm x = PiTensorProduct.tprod k (fun _ => x) := by
  simp [forgetLiftAppV]
  erw [PiTensorProduct.subsingletonEquiv_symm_apply']
  rfl

/-- The `forgetLiftAppV` function takes an object `c` of type `C` and returns a isomorphism
between the objects obtained by applying the lift of `F` and that obtained by applying
`F`. -/
def forgetLiftApp (c : C) : (lift.obj F).obj (OverColor.mk (fun (_ : Fin 1) => c))
    ≅ F.obj (Discrete.mk c) :=
  Rep.mkIso <| Representation.Equiv.mk (forgetLiftAppV F c)
  (fun g => by
    refine LinearMap.ext (fun x => ?_)
    simp only [forgetLiftAppV, Fin.isValue]
    refine PiTensorProduct.induction_on' x (fun r x => ?_) <| fun x y hx hy => by
      simp_rw [map_add, hx, hy]
    simp only [Fin.isValue,
      PiTensorProduct.tprodCoeff_eq_smul_tprod, map_smul, LinearMap.coe_comp,
      Function.comp_apply]
    apply congrArg
    erw [PiTensorProduct.subsingletonEquiv_apply_tprod]
    erw [lift.toRep_ρ_tprod]
    erw [PiTensorProduct.subsingletonEquiv_apply_tprod]
    rfl)

lemma forgetLiftApp_naturality_eqToHom (c c1 : C) (h : c = c1) :
    (forgetLiftApp F c).hom ≫ F.map (Discrete.eqToHom h) =
    (lift.obj F).map (OverColor.mkIso (by rw [h])).hom ≫ (forgetLiftApp F c1).hom := by
  subst h
  simp [mkIso_refl_hom]

lemma forgetLiftApp_naturality_eqToHom_apply (c c1 : C) (h : c = c1)
    (x : (lift.obj F).obj (OverColor.mk (fun (_ : Fin 1) => c))) :
    (F.map (Discrete.eqToHom h)).hom ((forgetLiftApp F c).hom.hom x) =
    (forgetLiftApp F c1).hom.hom (((lift.obj F).map (OverColor.mkIso (by rw [h])).hom).hom x) := by
  change ((forgetLiftApp F c).hom ≫ F.map (Discrete.eqToHom h)).hom x = _
  rw [forgetLiftApp_naturality_eqToHom]
  rfl

lemma forgetLiftApp_hom_hom_apply_eq (c : C)
    (x : (lift.obj F).obj (OverColor.mk (fun (_ : Fin 1) => c)))
    (y : (F.obj (Discrete.mk c)).V) :
    (forgetLiftApp F c).hom.hom x = y ↔ x = PiTensorProduct.tprod k (fun _ => y) := by
  rw [← forgetLiftAppV_symm_apply]
  erw [LinearEquiv.eq_symm_apply]
  rfl

/-- The isomorphism between the representation `(lift.obj F).obj (OverColor.mk ![c])`
  and the representation `F.obj (Discrete.mk c)`. See `forgetLiftApp` for
  an alternative version. -/
def forgetLiftAppCon (c : C) : (lift.obj F).obj (OverColor.mk ![c])
    ≅ F.obj (Discrete.mk c) := ((lift.obj F).mapIso (OverColor.mkIso (by
  funext i
  fin_cases i
  rfl))).trans (forgetLiftApp F c)

lemma forgetLiftAppCon_inv_apply_expand (c : C) (x : F.obj (Discrete.mk c)) :
    (forgetLiftAppCon F c).inv.hom x =
    ((lift.obj F).map (OverColor.mkIso (by
    funext i
    fin_cases i
    rfl)).hom).hom ((forgetLiftApp F c).inv.hom x) := by
  rw [forgetLiftAppCon]
  simp_all only [Nat.succ_eq_add_one, Iso.trans_inv, Functor.mapIso_inv]
  rfl

lemma forgetLiftAppCon_naturality_eqToHom (c c1 : C) (h : c = c1) :
    (forgetLiftAppCon F c).hom ≫ F.map (Discrete.eqToHom h) =
    (lift.obj F).map (OverColor.mkIso (by rw [h])).hom ≫ (forgetLiftAppCon F c1).hom := by
  subst h
  simp [mkIso_refl_hom]

lemma forgetLiftAppCon_naturality_eqToHom_apply (c c1 : C) (h : c = c1)
    (x : (lift.obj F).obj (OverColor.mk ![c])) :
    (F.map (Discrete.eqToHom h)).hom ((forgetLiftAppCon F c).hom.hom x) =
    (forgetLiftAppCon F c1).hom.hom
    (((lift.obj F).map (OverColor.mkIso (by rw [h])).hom).hom x) := by
  change ((forgetLiftAppCon F c).hom ≫ F.map (Discrete.eqToHom h)).hom x = _
  rw [forgetLiftAppCon_naturality_eqToHom]
  rfl

/-- Naturality of `forgetLiftApp` with respect to a natural transformation on singleton colors. -/
lemma forgetLiftApp_naturality {F F' : Discrete C ⥤ Rep k G} (η : F ⟶ F') (c : C) :
    ((lift.map η).hom.hom.app (incl.obj (Discrete.mk c))) ≫ (forgetLiftApp F' c).hom =
    (forgetLiftApp F c).hom ≫ η.app (Discrete.mk c) := by
  ext x
  refine PiTensorProduct.induction_on' x ?_ (by
    intro x y hx hy
    change (((lift.map η).hom.hom.app (incl.obj (Discrete.mk c))) ≫
        (forgetLiftApp F' c).hom).hom.toLinearMap (x + y) =
      ((forgetLiftApp F c).hom ≫ η.app (Discrete.mk c)).hom.toLinearMap (x + y)
    change (((lift.map η).hom.hom.app (incl.obj (Discrete.mk c))) ≫
        (forgetLiftApp F' c).hom).hom.toLinearMap x =
      ((forgetLiftApp F c).hom ≫ η.app (Discrete.mk c)).hom.toLinearMap x at hx
    change (((lift.map η).hom.hom.app (incl.obj (Discrete.mk c))) ≫
        (forgetLiftApp F' c).hom).hom.toLinearMap y =
      ((forgetLiftApp F c).hom ≫ η.app (Discrete.mk c)).hom.toLinearMap y at hy
    calc
      (((lift.map η).hom.hom.app (incl.obj (Discrete.mk c))) ≫
          (forgetLiftApp F' c).hom).hom.toLinearMap (x + y) =
        (((lift.map η).hom.hom.app (incl.obj (Discrete.mk c))) ≫
          (forgetLiftApp F' c).hom).hom.toLinearMap x +
        (((lift.map η).hom.hom.app (incl.obj (Discrete.mk c))) ≫
          (forgetLiftApp F' c).hom).hom.toLinearMap y := LinearMap.map_add _ _ _
      _ = ((forgetLiftApp F c).hom ≫ η.app (Discrete.mk c)).hom.toLinearMap x +
          ((forgetLiftApp F c).hom ≫ η.app (Discrete.mk c)).hom.toLinearMap y :=
        congrArg₂ (fun a b => a + b) hx hy
      _ = ((forgetLiftApp F c).hom ≫ η.app (Discrete.mk c)).hom.toLinearMap (x + y) :=
        (LinearMap.map_add _ _ _).symm)
  intro r p
  rw [PiTensorProduct.tprodCoeff_eq_smul_tprod]
  have hpure : (((lift.map η).hom.hom.app (incl.obj (Discrete.mk c))) ≫
        (forgetLiftApp F' c).hom).hom.toLinearMap ((PiTensorProduct.tprod k) p) =
      ((forgetLiftApp F c).hom ≫ η.app (Discrete.mk c)).hom.toLinearMap
        ((PiTensorProduct.tprod k) p) := by
    change (forgetLiftApp F' c).hom.hom
        (((lift.map η).hom.hom.app (incl.obj (Discrete.mk c))).hom.toLinearMap
          ((PiTensorProduct.tprod k) p)) =
      (η.app (Discrete.mk c)).hom.toLinearMap
        ((forgetLiftApp F c).hom.hom ((PiTensorProduct.tprod k) p))
    simp only [forgetLiftApp]
    rw [show ((lift.map η).hom.hom.app (incl.obj (Discrete.mk c))).hom.toLinearMap
        ((PiTensorProduct.tprod k) p) =
        (lift.repNatTransOfColorApp η (incl.obj (Discrete.mk c))).hom.toLinearMap
          ((PiTensorProduct.tprod k) p) by
        rfl]
    change (forgetLiftAppV F' c)
        ((lift.repNatTransOfColorApp η (incl.obj (Discrete.mk c))).hom
          ((PiTensorProduct.tprod k) p)) =
      (η.app (Discrete.mk c)).hom.toLinearMap
        ((forgetLiftAppV F c) ((PiTensorProduct.tprod k) p))
    rw [lift.repNatTransOfColorApp_tprod]
    erw [PiTensorProduct.subsingletonEquiv_apply_tprod]
    erw [PiTensorProduct.subsingletonEquiv_apply_tprod]
    rfl
  change (((lift.map η).hom.hom.app (incl.obj (Discrete.mk c))) ≫
      (forgetLiftApp F' c).hom).hom.toLinearMap (r • (PiTensorProduct.tprod k) p) =
    ((forgetLiftApp F c).hom ≫ η.app (Discrete.mk c)).hom.toLinearMap
      (r • (PiTensorProduct.tprod k) p)
  exact calc
    (((lift.map η).hom.hom.app (incl.obj (Discrete.mk c))) ≫
        (forgetLiftApp F' c).hom).hom.toLinearMap (r • (PiTensorProduct.tprod k) p) =
      r • (((lift.map η).hom.hom.app (incl.obj (Discrete.mk c))) ≫
        (forgetLiftApp F' c).hom).hom.toLinearMap ((PiTensorProduct.tprod k) p) :=
        LinearMap.map_smul _ _ _
    _ = r • ((forgetLiftApp F c).hom ≫ η.app (Discrete.mk c)).hom.toLinearMap
        ((PiTensorProduct.tprod k) p) := congrArg (fun z => r • z) hpure
    _ = ((forgetLiftApp F c).hom ≫ η.app (Discrete.mk c)).hom.toLinearMap
        (r • (PiTensorProduct.tprod k) p) := (LinearMap.map_smul _ _ _).symm

/-- The natural isomorphism between `lift (C := C) ⋙ forget` and
`Functor.id (Discrete C ⥤ Rep k G)`.
-/
noncomputable def forgetLift : lift (C := C) ⋙ forget ≅ Functor.id (Discrete C ⥤ Rep k G) :=
  NatIso.ofComponents
    (fun F => {
      hom := Discrete.natTrans fun c => (forgetLiftApp F c.as).hom
      inv := Discrete.natTrans fun c => (forgetLiftApp F c.as).inv
      hom_inv_id := by
        ext c x
        simp
      inv_hom_id := by
        ext c x
        simp })
    (by
      intro F F' η
      ext c x
      simpa [forget] using congrArg (fun f => f.hom x) (forgetLiftApp_naturality η c.as))

end
end OverColor
end IndexNotation
