/-
Copyright (c) 2025 Benoît Guillemet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benoît Guillemet
-/
import Mathlib.CategoryTheory.Closed.Types
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.Sites.Preserves
import Mathlib.Condensed.Functors
import Mathlib.Condensed.Limits
import Mathlib.Condensed.Equivalence
import Mathlib.CategoryTheory.Limits.MonoCoprod


/-!
In this file, we show that the functor `compHausToCondensed` preserves finite coproducts.
-/

universe u v w

open CategoryTheory Limits Functor

namespace Condensed

attribute [local instance] Types.instConcreteCategory

variable {I : Type} [Finite I] (X : CondensedSet.{u})

abbrev evaluation := CategoryTheory.evaluation _ _ ⋙
  (whiskeringLeft _ _ _).obj (sheafToPresheaf (coherentTopology CompHaus.{u}) (Type (u + 1)))

@[simps!]
noncomputable def valObjLimitIso (S : (Discrete I)ᵒᵖ ⥤ CompHausᵒᵖ) (X : CondensedSet.{u}) :
    X.val.obj (limit S)
    ≅ (limit (S ⋙ evaluation)).obj X :=
  have := preservesLimitsOfShape_of_equiv (Discrete.opposite I).symm X.val
  (preservesLimitIso X.val S).trans (limitObjIsoLimitCompEvaluation (S ⋙ evaluation) X).symm

noncomputable def sheafToPresheafCompEvaluationLimitNatIso (S : (Discrete I)ᵒᵖ ⥤ CompHausᵒᵖ) :
    sheafToPresheaf (coherentTopology CompHaus) (Type (u + 1))
    ⋙ (CategoryTheory.evaluation _ _).obj (limit S)
    ≅ limit (S ⋙ evaluation) := by
  refine NatIso.ofComponents (valObjLimitIso S) (fun {X Y} f => ?_)
  have := preservesLimitsOfShape_of_equiv (Discrete.opposite I).symm X.val
  have := preservesLimitsOfShape_of_equiv (Discrete.opposite I).symm Y.val
  ext x
  set F := S ⋙ evaluation
  change _ = ((limitObjIsoLimitCompEvaluation _ _).inv ≫ (limit F).map _) _
  rw [limitObjIsoLimitCompEvaluation_inv_limit_map F f]
  refine congrArg _ (Types.limit_ext _ _ _ (fun j => ?_))
  change ((preservesLimitIso Y.val S).hom ≫ (limit.π (S ⋙ Y.val) j)) _
    = (limMap (whiskerLeft F ((CategoryTheory.evaluation _ _).map f))
    ≫ limit.π (F ⋙ (CategoryTheory.evaluation _ _).obj Y) j) _
  rw [limMap_π, preservesLimitIso_hom_π]
  change (f.val.app (limit S) ≫ Y.val.map (limit.π S j)) _ = _
  rw [← f.val.naturality (limit.π S j)]
  change _ = (F.obj j).map f (((preservesLimitIso X.val S).hom ≫ limit.π (S ⋙ X.val) j) x)
  rw [preservesLimitIso_hom_π]
  rfl

@[simp]
lemma sheafToPresheafCompEvaluationLimitIso_hom_π (S : (Discrete I) ⥤ CompHaus.{u})
    (j : Discrete I) :
    (sheafToPresheafCompEvaluationLimitNatIso S.op).hom ≫ limit.π _ (Opposite.op j)
    = evaluation.map (limit.π _ (Opposite.op j)) := by
  ext X (x : X.val.obj (limit S.op))
  have := preservesLimitsOfShape_of_equiv (Discrete.opposite I).symm X.val
  change ((preservesLimitIso X.val S.op).hom ≫ (limitObjIsoLimitCompEvaluation
    (S.op ⋙ evaluation) X).inv
    ≫ ((limit.π (S.op ⋙ evaluation) _).app X)) _ = _
  simp only [comp_obj, op_obj, whiskeringLeft_obj_obj, sheafToPresheaf_obj, evaluation_obj_obj,
    limitObjIsoLimitCompEvaluation_inv_π_app, types_comp_apply, Functor.comp_map,
    whiskeringLeft_obj_map, whiskerLeft_app, evaluation_map_app, ← preservesLimitIso_hom_π]
  rfl

def condensedYonedaEquiv {S : CompHaus.{u}} {X : CondensedSet.{u}} :
    (compHausToCondensed.obj S ⟶ X) ≃ X.val.obj (Opposite.op S) :=
  (coherentTopology CompHaus).uliftYonedaEquiv

noncomputable def condensedYonedaLemma :
    compHausToCondensed.op ⋙ coyoneda ≅ evaluation :=
  (coherentTopology CompHaus).largeCurriedUliftYonedaLemma ≪≫
    isoWhiskerLeft _ (isoWhiskerRight ((whiskeringRight _ _ _).mapIso uliftFunctorTrivial) _)

noncomputable def coyonedaOpCompHausToCondensedFiniteCoproductNatIso
    (S : Discrete I ⥤ CompHaus.{u}) :
    coyoneda.obj (Opposite.op (compHausToCondensed.obj (colimit S)))
    ≅ coyoneda.obj (Opposite.op (colimit (S ⋙ compHausToCondensed))) :=
  condensedYonedaLemma.app (Opposite.op (colimit S)) ≪≫
    (_ ⋙ _).mapIso (limitOpIsoOpColimit _).symm ≪≫
    sheafToPresheafCompEvaluationLimitNatIso S.op ≪≫
    (HasLimit.isoOfNatIso (isoWhiskerLeft S.op condensedYonedaLemma.symm)) ≪≫
    (preservesLimitIso coyoneda (S ⋙ compHausToCondensed).op).symm ≪≫
    coyoneda.mapIso (limitOpIsoOpColimit _)

@[simp]
lemma coyonedaOpCompHausToCondensedFiniteCoproductNatIso_hom (S : Discrete I ⥤ CompHaus.{u}) :
    (coyonedaOpCompHausToCondensedFiniteCoproductNatIso S).hom
    = coyoneda.map (colimit.post S compHausToCondensed).op := by
  unfold coyonedaOpCompHausToCondensedFiniteCoproductNatIso
  simp only [comp_obj, whiskeringLeft_obj_obj, mapIso_symm, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, mapIso_inv, Functor.comp_map, whiskeringLeft_obj_map, ← Category.assoc]
  rw [← Iso.eq_comp_inv, Iso.comp_inv_eq, ← Iso.eq_comp_inv]
  apply limit.hom_ext fun j => ?_
  simp only [comp_obj, op_obj, whiskeringLeft_obj_obj, Category.assoc, mapIso_inv]
  rw [sheafToPresheafCompEvaluationLimitIso_hom_π]
  ext X (f : compHausToCondensed.obj (colimit S) ⟶ X)
  have h₁ : (condensedYonedaLemma.hom.app (Opposite.op (colimit S))).app X f
      = condensedYonedaEquiv f := rfl
  have h₂ : X.val.map (limit.π S.op j)
      (X.val.map (limitOpIsoOpColimit S).inv (condensedYonedaEquiv f))
      = condensedYonedaEquiv (compHausToCondensed.map (colimit.ι S j.unop) ≫ f) := by
    change (f.val.app _ ≫ _ ≫ _) _ = _
    rw [← X.val.map_comp, ← f.val.naturality, limitOpIsoOpColimit_inv_comp_π]
    rfl
  simp only [comp_obj, sheafToPresheaf_obj, evaluation_obj_obj, Opposite.op_unop, op_obj,
    Functor.comp_map, whiskeringLeft_obj_map, FunctorToTypes.comp, whiskerLeft_app,
    evaluation_map_app, flip_map_app, yoneda_obj_map, Quiver.Hom.unop_op]
  change _ = ((preservesLimitIso coyoneda (S ⋙ compHausToCondensed).op).hom
    ≫ (HasLimit.isoOfNatIso (S.op.isoWhiskerLeft condensedYonedaLemma.symm)).inv
    ≫ limit.π _ j).app X _
  rw [h₁, h₂, HasLimit.isoOfNatIso_inv_π]
  change _ = (((preservesLimitIso coyoneda (S ⋙ compHausToCondensed).op).hom
    ≫ limit.π _ j)
    ≫ (S.op.isoWhiskerLeft condensedYonedaLemma.symm).inv.app j).app X _
  rw [preservesLimitIso_hom_π]
  simp only [comp_obj, op_obj, whiskeringLeft_obj_obj, sheafToPresheaf_obj, evaluation_obj_obj,
    isoWhiskerLeft_inv, Iso.symm_inv, whiskerLeft_app, FunctorToTypes.comp, flip_map_app,
    yoneda_obj_map]
  rw [← Category.assoc, ← unop_comp, limitOpIsoOpColimit_inv_comp_π, Quiver.Hom.unop_op,
    colimit.ι_post_assoc]
  rfl

noncomputable def compHausToCondensedColimitIso (S : Discrete I ⥤ CompHaus.{u}) :
    compHausToCondensed.obj (colimit S) ≅ colimit (S ⋙ compHausToCondensed) :=
  (Coyoneda.fullyFaithful.preimageIso
    (coyonedaOpCompHausToCondensedFiniteCoproductNatIso S).symm).unop

@[simp]
lemma compHausToCondensedFiniteCoproductIso_inv (S : Discrete I ⥤ CompHaus.{u}) :
    (compHausToCondensedColimitIso S).inv = colimit.post S compHausToCondensed := by
  simp [compHausToCondensedColimitIso]

instance (S : Discrete I ⥤ CompHaus.{u}) :
    IsIso (colimit.post S compHausToCondensed) := by
  rw [← compHausToCondensedFiniteCoproductIso_inv]
  infer_instance

instance : PreservesFiniteCoproducts compHausToCondensed.{u} where
  preserves _ :=  { preservesColimit := preservesColimit_of_isIso_post _ _ }

@[simp]
lemma preservesColimitIso_compHausToCondensed {n : ℕ} (S : Discrete (Fin n) ⥤ CompHaus.{u}) :
    preservesColimitIso compHausToCondensed.{u} S = compHausToCondensedColimitIso S := by
  refine Iso.symm_eq_iff.1 (Iso.ext (colimit.hom_ext ?_))
  simp

end Condensed
