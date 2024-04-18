# The universal property of sequential colimits

```agda
{-# OPTIONS --allow-unsolved-metas #-}
module synthetic-homotopy-theory.universal-property-sequential-colimits where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.precomposition-functions
open import foundation.retractions
open import foundation.sections
open import foundation.subtype-identity-principle
open import foundation.transposition-identifications-along-equivalences
open import foundation.universal-property-equivalences
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.composite-maps-sequential-diagrams
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.universal-property-coequalizers
```

</details>

## Idea

Given a [sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md)
`(A, a)`, consider a
[cocone under it](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md)
`c` with vertex `X`. The **universal property of sequential colimits** is the
statement that the cocone postcomposition map

```text
cocone-map-sequential-diagram : (X → Y) → cocone-sequential-diagram Y
```

is an [equivalence](foundation.equivalences.md).

A sequential colimit `X` may be visualized as a "point in infinity" in the
diagram

```text
     a₀      a₁      a₂     i
 A₀ ---> A₁ ---> A₂ ---> ⋯ --> X.
```

## Definitions

### The universal property of sequential colimits

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  universal-property-sequential-colimit : UUω
  universal-property-sequential-colimit =
    {l : Level} → (Y : UU l) →
    is-equiv (cocone-map-sequential-diagram c {Y = Y})
```

### The map induced by the universal property of sequential colimits

The universal property allows us to construct a map from the colimit by
providing a cocone under the sequential diagram.

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2}
  { c : cocone-sequential-diagram A X} {Y : UU l3}
  ( up-sequential-colimit : universal-property-sequential-colimit c)
  where

  equiv-universal-property-sequential-colimit :
    (X → Y) ≃ cocone-sequential-diagram A Y
  pr1 equiv-universal-property-sequential-colimit =
    cocone-map-sequential-diagram c
  pr2 equiv-universal-property-sequential-colimit =
    up-sequential-colimit Y

  map-universal-property-sequential-colimit :
    cocone-sequential-diagram A Y → (X → Y)
  map-universal-property-sequential-colimit =
    map-inv-is-equiv (up-sequential-colimit Y)
```

## Properties

### The mediating map obtained by the universal property is unique

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1}
  { X : UU l2} {c : cocone-sequential-diagram A X}
  ( up-sequential-colimit : universal-property-sequential-colimit c)
  { Y : UU l3} (c' : cocone-sequential-diagram A Y)
  where

  htpy-cocone-universal-property-sequential-colimit :
    htpy-cocone-sequential-diagram
      ( cocone-map-sequential-diagram c
        ( map-universal-property-sequential-colimit
          ( up-sequential-colimit)
          ( c')))
      ( c')
  htpy-cocone-universal-property-sequential-colimit =
    htpy-eq-cocone-sequential-diagram A
      ( cocone-map-sequential-diagram c
        ( map-universal-property-sequential-colimit
          ( up-sequential-colimit)
          ( c')))
      ( c')
      ( is-section-map-inv-is-equiv (up-sequential-colimit Y) c')

  htpy-htpy-cocone-universal-property-sequential-colimit :
    (n : ℕ) →
    coherence-triangle-maps'
      ( map-cocone-sequential-diagram c' n)
      ( map-universal-property-sequential-colimit up-sequential-colimit c')
      ( map-cocone-sequential-diagram c n)
  htpy-htpy-cocone-universal-property-sequential-colimit =
    htpy-htpy-cocone-sequential-diagram
      ( htpy-cocone-universal-property-sequential-colimit)

  coherence-htpy-htpy-cocone-universal-property-sequential-colimit :
    (n : ℕ) →
    coherence-square-homotopies
      ( htpy-htpy-cocone-universal-property-sequential-colimit n)
      ( ( map-universal-property-sequential-colimit up-sequential-colimit c') ·l
        ( coherence-cocone-sequential-diagram c n))
      ( coherence-cocone-sequential-diagram c' n)
      ( ( htpy-htpy-cocone-universal-property-sequential-colimit (succ-ℕ n)) ·r
        ( map-sequential-diagram A n))
  coherence-htpy-htpy-cocone-universal-property-sequential-colimit =
    coherence-htpy-htpy-cocone-sequential-diagram
      ( htpy-cocone-universal-property-sequential-colimit)

  abstract
    uniqueness-map-universal-property-sequential-colimit :
      is-contr
        ( Σ ( X → Y)
            ( λ h →
              htpy-cocone-sequential-diagram
                ( cocone-map-sequential-diagram c h)
                ( c')))
    uniqueness-map-universal-property-sequential-colimit =
      is-contr-equiv'
        ( fiber (cocone-map-sequential-diagram c) c')
        ( equiv-tot
          ( λ h →
            extensionality-cocone-sequential-diagram A
              ( cocone-map-sequential-diagram c h)
              ( c')))
        ( is-contr-map-is-equiv (up-sequential-colimit Y) c')
```

### TODO title

up-c c ~ id

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1}
  { X : UU l2} {c : cocone-sequential-diagram A X}
  ( up-c : universal-property-sequential-colimit c)
  where

  bla : map-universal-property-sequential-colimit up-c c ~ (λ x → x)
  bla =
    htpy-eq
      ( map-eq-transpose-equiv-inv
        ( equiv-universal-property-sequential-colimit up-c)
        ( inv
          ( cocone-map-id-sequential-diagram A c)))
```


### Correspondence between universal properties of sequential colimits and coequalizers

A cocone under a sequential diagram has the universal property of sequential
colimits if and only if the
[corresponding cofork](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md)
has the universal property of coequalizers.

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  universal-property-sequential-colimit-universal-property-coequalizer :
    ( {l : Level} →
      universal-property-coequalizer l
        ( bottom-map-cofork-cocone-sequential-diagram A)
        ( top-map-cofork-cocone-sequential-diagram A)
        ( cofork-cocone-sequential-diagram A c)) →
    universal-property-sequential-colimit c
  universal-property-sequential-colimit-universal-property-coequalizer
    ( up-cofork)
    ( Y) =
    is-equiv-left-map-triangle
      ( cocone-map-sequential-diagram c)
      ( cocone-sequential-diagram-cofork A)
      ( cofork-map
        ( bottom-map-cofork-cocone-sequential-diagram A)
        ( top-map-cofork-cocone-sequential-diagram A)
        ( cofork-cocone-sequential-diagram A c))
      ( triangle-cocone-sequential-diagram-cofork A c)
      ( up-cofork Y)
      ( is-equiv-cocone-sequential-diagram-cofork A)

  universal-property-coequalizer-universal-property-sequential-colimit :
    universal-property-sequential-colimit c →
    ( {l : Level} →
      universal-property-coequalizer l
        ( bottom-map-cofork-cocone-sequential-diagram A)
        ( top-map-cofork-cocone-sequential-diagram A)
        ( cofork-cocone-sequential-diagram A c))
  universal-property-coequalizer-universal-property-sequential-colimit
    ( up-sequential-colimit)
    ( Y) =
    is-equiv-top-map-triangle
      ( cocone-map-sequential-diagram c)
      ( cocone-sequential-diagram-cofork A)
      ( cofork-map
        ( bottom-map-cofork-cocone-sequential-diagram A)
        ( top-map-cofork-cocone-sequential-diagram A)
        ( cofork-cocone-sequential-diagram A c))
      ( triangle-cocone-sequential-diagram-cofork A c)
      ( is-equiv-cocone-sequential-diagram-cofork A)
      ( up-sequential-colimit Y)
```

### The 3-for-2 property of the universal property of sequential colimits

Given two cocones under a sequential diagram, one of which has the universal
property of sequential colimits, and a map between their vertices, we prove that
the other has the universal property if and only if the map is an
[equivalence](foundation.equivalences.md).

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2} {Y : UU l3}
  ( c : cocone-sequential-diagram A X)
  ( c' : cocone-sequential-diagram A Y)
  ( h : X → Y)
  ( H :
    htpy-cocone-sequential-diagram (cocone-map-sequential-diagram c h) c')
  where

  inv-triangle-cocone-map-precomp-sequential-diagram :
    { l4 : Level} (Z : UU l4) →
    coherence-triangle-maps'
      ( cocone-map-sequential-diagram c')
      ( cocone-map-sequential-diagram c)
      ( precomp h Z)
  inv-triangle-cocone-map-precomp-sequential-diagram Z k =
    ( cocone-map-comp-sequential-diagram A c h k) ∙
    ( ap
      ( λ d → cocone-map-sequential-diagram d k)
      ( eq-htpy-cocone-sequential-diagram A
        ( cocone-map-sequential-diagram c h)
        ( c')
        ( H)))

  triangle-cocone-map-precomp-sequential-diagram :
    { l4 : Level} (Z : UU l4) →
    coherence-triangle-maps
      ( cocone-map-sequential-diagram c')
      ( cocone-map-sequential-diagram c)
      ( precomp h Z)
  triangle-cocone-map-precomp-sequential-diagram Z =
    inv-htpy (inv-triangle-cocone-map-precomp-sequential-diagram Z)

  abstract
    is-equiv-universal-property-sequential-colimit-universal-property-sequential-colimit :
      universal-property-sequential-colimit c →
      universal-property-sequential-colimit c' →
      is-equiv h
    is-equiv-universal-property-sequential-colimit-universal-property-sequential-colimit
      ( up-sequential-colimit)
      ( up-sequential-colimit') =
      is-equiv-is-equiv-precomp h
        ( λ Z →
          is-equiv-top-map-triangle
            ( cocone-map-sequential-diagram c')
            ( cocone-map-sequential-diagram c)
            ( precomp h Z)
            ( triangle-cocone-map-precomp-sequential-diagram Z)
            ( up-sequential-colimit Z)
            ( up-sequential-colimit' Z))

    universal-property-sequential-colimit-is-equiv-universal-property-sequential-colimit :
      universal-property-sequential-colimit c →
      is-equiv h →
      universal-property-sequential-colimit c'
    universal-property-sequential-colimit-is-equiv-universal-property-sequential-colimit
      ( up-sequential-colimit)
      ( is-equiv-h)
      ( Z) =
      is-equiv-left-map-triangle
        ( cocone-map-sequential-diagram c')
        ( cocone-map-sequential-diagram c)
        ( precomp h Z)
        ( triangle-cocone-map-precomp-sequential-diagram Z)
        ( is-equiv-precomp-is-equiv h is-equiv-h Z)
        ( up-sequential-colimit Z)

    universal-property-sequential-colimit-universal-property-sequential-colimit-is-equiv :
      is-equiv h →
      universal-property-sequential-colimit c' →
      universal-property-sequential-colimit c
    universal-property-sequential-colimit-universal-property-sequential-colimit-is-equiv
      ( is-equiv-h)
      ( up-sequential-colimit)
      ( Z) =
      is-equiv-right-map-triangle
        ( cocone-map-sequential-diagram c')
        ( cocone-map-sequential-diagram c)
        ( precomp h Z)
        ( triangle-cocone-map-precomp-sequential-diagram Z)
        ( up-sequential-colimit Z)
        ( is-equiv-precomp-is-equiv h is-equiv-h Z)
```

### Unique uniqueness of sequential colimits

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2} {Y : UU l3}
  { c : cocone-sequential-diagram A X}
  ( up-c : universal-property-sequential-colimit c)
  { c' : cocone-sequential-diagram A Y}
  ( up-c' : universal-property-sequential-colimit c')
  where

  abstract
    uniquely-unique-sequential-colimit :
      is-contr
        ( Σ ( X ≃ Y)
            ( λ e →
              htpy-cocone-sequential-diagram
                ( cocone-map-sequential-diagram c (map-equiv e))
                ( c')))
    uniquely-unique-sequential-colimit =
      is-torsorial-Eq-subtype
        ( uniqueness-map-universal-property-sequential-colimit up-c c')
        ( is-property-is-equiv)
        ( map-universal-property-sequential-colimit up-c c')
        ( htpy-cocone-universal-property-sequential-colimit up-c c')
        ( is-equiv-universal-property-sequential-colimit-universal-property-sequential-colimit
          ( c)
          ( c')
          ( map-universal-property-sequential-colimit up-c c')
          ( htpy-cocone-universal-property-sequential-colimit up-c c')
          ( up-c)
          ( up-c'))
```

### TODO title

```agda
module _
  { l1 : Level} (X : UU l1)
  where

  cocone-const-sequential-diagram :
    cocone-sequential-diagram (constant-sequential-diagram X) X
  pr1 cocone-const-sequential-diagram n x = x
  pr2 cocone-const-sequential-diagram n x = refl

  module _
    {l : Level} (Y : UU l)
    where

    map-inv-cocone-map-constant-sequential-diagram :
      cocone-sequential-diagram (constant-sequential-diagram X) Y →
      X → Y
    map-inv-cocone-map-constant-sequential-diagram c x =
      map-cocone-sequential-diagram c 0 x

    htpy-blabla :
      (c : cocone-sequential-diagram (constant-sequential-diagram X) Y) →
      htpy-cocone-sequential-diagram
        ( cocone-map-sequential-diagram
          ( cocone-const-sequential-diagram)
          ( map-inv-cocone-map-constant-sequential-diagram c))
        ( c)
    pr1 (htpy-blabla c) n x =
      coherence-comp-foo-map-cocone-sequential-diagram c n x ∙
      ap (pr1 c n) (comp-foo-map-const-sequential-diagram X n x)
    pr2 (htpy-blabla c) zero-ℕ = right-unit-htpy
    pr2 (htpy-blabla c) (succ-ℕ n) x =
      {!!}
      -- left-whisk-square-identification
      --  (coherence-comp-foo-map-cocone-sequential-diagram c n x ∙
      --   pr2 c n
      --   (comp-foo-map-sequential-diagram (constant-sequential-diagram X) n
      --    x))
      --  {!!}

    is-section-map-inv-cocone-map-constant-sequential-diagram :
      is-section
        ( cocone-map-sequential-diagram cocone-const-sequential-diagram)
        ( map-inv-cocone-map-constant-sequential-diagram)
    is-section-map-inv-cocone-map-constant-sequential-diagram c =
      eq-htpy-cocone-sequential-diagram
        ( constant-sequential-diagram X)
        ( _)
        ( _)
        ( htpy-blabla c)

    is-retraction-map-inv-cocone-map-constant-sequential-diagram :
      is-retraction
        ( cocone-map-sequential-diagram cocone-const-sequential-diagram)
        ( map-inv-cocone-map-constant-sequential-diagram)
    is-retraction-map-inv-cocone-map-constant-sequential-diagram = refl-htpy

  up-sequential-colimit-constant-sequential-diagram :
    universal-property-sequential-colimit cocone-const-sequential-diagram
  up-sequential-colimit-constant-sequential-diagram Y =
    is-equiv-is-invertible
      ( map-inv-cocone-map-constant-sequential-diagram Y)
      ( is-section-map-inv-cocone-map-constant-sequential-diagram Y)
      ( is-retraction-map-inv-cocone-map-constant-sequential-diagram Y)
```
