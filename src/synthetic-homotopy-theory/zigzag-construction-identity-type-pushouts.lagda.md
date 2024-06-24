# The zigzag construction of identity types of pushouts

```agda
{-# OPTIONS --lossy-unification --allow-unsolved-metas #-}

module synthetic-homotopy-theory.zigzag-construction-identity-type-pushouts where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

-- open import foundation.commuting-squares-of-maps
-- open import foundation.contractible-types
open import foundation.action-on-identifications-dependent-functions
open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-homotopies
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
-- open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-algebra
-- open import foundation.identity-systems
open import foundation.identity-types
-- open import foundation.sections
-- open import foundation.singleton-induction
open import foundation.raising-universe-levels
open import foundation.span-diagrams
open import foundation.transport-along-identifications
open import foundation.transposition-identifications-along-equivalences
-- open import foundation.torsorial-type-families
-- open import foundation.transposition-identifications-along-equivalences
-- open import foundation.universal-property-dependent-pair-types
-- open import foundation.universal-property-identity-types
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-higher-homotopies-composition
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.cocones-under-spans
-- open import synthetic-homotopy-theory.dependent-universal-property-pushouts
-- open import synthetic-homotopy-theory.descent-data-equivalence-types-over-pushouts
-- open import synthetic-homotopy-theory.descent-data-identity-types-over-pushouts
open import synthetic-homotopy-theory.dependent-cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-universal-property-sequential-colimits
open import synthetic-homotopy-theory.descent-data-pushouts
open import synthetic-homotopy-theory.functoriality-sequential-colimits
open import synthetic-homotopy-theory.identity-systems-descent-data-pushouts
-- open import synthetic-homotopy-theory.descent-property-pushouts
-- open import synthetic-homotopy-theory.equivalences-descent-data-pushouts
open import synthetic-homotopy-theory.families-descent-data-pushouts
open import synthetic-homotopy-theory.flattening-lemma-pushouts
-- open import synthetic-homotopy-theory.morphisms-descent-data-pushouts
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.sequential-colimits
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.shifts-sequential-diagrams
open import synthetic-homotopy-theory.sections-descent-data-pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
open import synthetic-homotopy-theory.zigzags-sequential-diagrams
```

</details>

## Idea

TODO

## Definitions

### TODO

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
-- open import synthetic-homotopy-theory.dependent-universal-property-sequential-colimits
open import synthetic-homotopy-theory.universal-property-sequential-colimits
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : sequential-diagram l1} {B : sequential-diagram l2}
  {X : UU l3} {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  {Y : UU l4} {c' : cocone-sequential-diagram B Y}
  (up-c' : universal-property-sequential-colimit c')
  (z : zigzag-sequential-diagram A B)
  (P : X → UU l5) (Q : Y → UU l6)
  (e : (x : X) → P x ≃ Q (map-colimit-zigzag-sequential-diagram up-c up-c' z x))
  where

  private
    CB :
      (n : ℕ) →
      coherence-square-maps
        ( map-zigzag-sequential-diagram z n)
        ( map-cocone-sequential-diagram c n)
        ( map-cocone-sequential-diagram c' n)
        ( map-colimit-zigzag-sequential-diagram up-c up-c' z)
    CB =
       htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
        ( up-c)
        ( c')
        ( hom-diagram-zigzag-sequential-diagram z)
    dup-c : dependent-universal-property-sequential-colimit c
    dup-c = dependent-universal-property-universal-property-sequential-colimit _ up-c
    dup-c' : dependent-universal-property-sequential-colimit c'
    dup-c' = dependent-universal-property-universal-property-sequential-colimit _ up-c'

  tS-equiv-tS :
    (tA : (n : ℕ) (a : family-sequential-diagram A n) → P (map-cocone-sequential-diagram c n a))
    (HA :
      (n : ℕ) (a : family-sequential-diagram A n) →
      tr P (coherence-cocone-sequential-diagram c n a) (tA n a) ＝
      tA (succ-ℕ n) (map-sequential-diagram A n a))
    (tB : (n : ℕ) (b : family-sequential-diagram B n) → Q (map-cocone-sequential-diagram c' n b))
    (HB :
      (n : ℕ) (b : family-sequential-diagram B n) →
      tr Q (coherence-cocone-sequential-diagram c' n b) (tB n b) ＝
      tB (succ-ℕ n) (map-sequential-diagram B n b))
    (n : ℕ) (a : family-sequential-diagram A n) →
    ( ( map-equiv
        ( e (map-cocone-sequential-diagram c n a))
        ( map-dependent-universal-property-sequential-colimit dup-c
          ( tA , HA)
          ( map-cocone-sequential-diagram c n a))) ＝
      map-dependent-universal-property-sequential-colimit dup-c'
        ( tB , HB)
        ( map-colimit-zigzag-sequential-diagram up-c up-c' z
          ( map-cocone-sequential-diagram c n a))) ≃
    ( ( tr Q
        ( CB n a)
        ( map-equiv (e (map-cocone-sequential-diagram c n a)) (tA n a))) ＝
      ( tB n (map-zigzag-sequential-diagram z n a)))
  tS-equiv-tS tA HA tB HB n a =
    ( equiv-concat' _
      ( pr1
        ( htpy-dependent-cocone-dependent-universal-property-sequential-colimit
          ( dup-c')
          ( tB , HB))
        ( n)
        ( map-zigzag-sequential-diagram z n a))) ∘e
    ( equiv-concat' _
      ( apd
        ( map-dependent-universal-property-sequential-colimit dup-c' (tB , HB))
        ( CB n a))) ∘e
    ( equiv-ap
      ( equiv-tr Q (CB n a))
      ( _)
      ( _)) ∘e
    equiv-concat
      ( ap
        ( map-equiv (e (map-cocone-sequential-diagram c n a)))
        ( inv
          ( pr1
            ( htpy-dependent-cocone-dependent-universal-property-sequential-colimit
              ( dup-c)
              ( tA , HA))
            ( n)
            ( a))))
      ( _)
```

```agda
module _
  {l1 l2 l3 : Level} (𝒮 : span-diagram l1 l2 l3)
  where

  type-stage-zigzag-construction-id-pushout : ℕ → UU (lsuc (l1 ⊔ l2 ⊔ l3))
  type-stage-zigzag-construction-id-pushout n =
    Σ ( codomain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3))
      ( λ Path-to-b →
        Σ ( domain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3))
          ( λ Path-to-a →
            ( Σ ( (s : spanning-type-span-diagram 𝒮) →
                  Path-to-b (right-map-span-diagram 𝒮 s) →
                  Path-to-a (left-map-span-diagram 𝒮 s))
                ( λ _ →
                  rec-ℕ
                    ( raise-unit (lsuc (l1 ⊔ l2 ⊔ l3)))
                    ( λ _ _ →
                      ( codomain-span-diagram 𝒮 →
                        span-diagram
                          ( l1 ⊔ l2 ⊔ l3)
                          ( l1 ⊔ l2 ⊔ l3)
                          ( l1 ⊔ l2 ⊔ l3)) ×
                      ( domain-span-diagram 𝒮 →
                        span-diagram
                          ( l1 ⊔ l2 ⊔ l3)
                          ( l1 ⊔ l2 ⊔ l3)
                          ( l1 ⊔ l2 ⊔ l3)))
                    ( n)))))

module _
  {l1 l2 l3 : Level} (𝒮 : span-diagram l1 l2 l3)
  (a₀ : domain-span-diagram 𝒮)
  where

  stage-zigzag-construction-id-pushout :
    (n : ℕ) → type-stage-zigzag-construction-id-pushout 𝒮 n
  stage-zigzag-construction-id-pushout zero-ℕ =
    Path-to-b ,
    Path-to-a ,
    ( λ s → raise-ex-falso _) ,
    raise-star
    where
    Path-to-b : codomain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3)
    Path-to-b _ = raise-empty _
    Path-to-a : domain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3)
    Path-to-a a = raise (l2 ⊔ l3) (a₀ ＝ a)
  stage-zigzag-construction-id-pushout (succ-ℕ n) =
    Path-to-b ,
    Path-to-a ,
    ( λ s p → inr-pushout _ _ (s , refl , p)) ,
    span-diagram-B ,
    span-diagram-A
    where
    span-diagram-B :
      codomain-span-diagram 𝒮 →
      span-diagram (l1 ⊔ l2 ⊔ l3) (l1 ⊔ l2 ⊔ l3) (l1 ⊔ l2 ⊔ l3)
    span-diagram-B b =
      make-span-diagram
        ( pr2 ∘ pr2)
        ( tot
          ( λ s →
            tot
              ( λ r (p : pr1 (stage-zigzag-construction-id-pushout n) b) →
                pr1
                  ( pr2 (pr2 (stage-zigzag-construction-id-pushout n)))
                  ( s)
                  ( tr (pr1 (stage-zigzag-construction-id-pushout n)) r p))))
    Path-to-b : codomain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3)
    Path-to-b b = standard-pushout (span-diagram-B b)
    span-diagram-A :
      domain-span-diagram 𝒮 →
      span-diagram (l1 ⊔ l2 ⊔ l3) (l1 ⊔ l2 ⊔ l3) (l1 ⊔ l2 ⊔ l3)
    span-diagram-A a =
      make-span-diagram
        ( pr2 ∘ pr2)
        ( tot
          ( λ s →
            tot
              ( λ r (p : pr1 (pr2 (stage-zigzag-construction-id-pushout n)) a) →
                inr-standard-pushout
                  ( span-diagram-B (right-map-span-diagram 𝒮 s))
                  ( ( s) ,
                    ( refl) ,
                    ( tr
                      ( pr1 (pr2 (stage-zigzag-construction-id-pushout n)))
                      ( r)
                      ( p))))))
    Path-to-a : domain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3)
    Path-to-a a = standard-pushout (span-diagram-A a)

  span-diagram-path-to-b :
    codomain-span-diagram 𝒮 → ℕ →
    span-diagram
      ( l1 ⊔ l2 ⊔ l3)
      ( l1 ⊔ l2 ⊔ l3)
      ( l1 ⊔ l2 ⊔ l3)
  span-diagram-path-to-b b n =
    pr1 (pr2 (pr2 (pr2 (stage-zigzag-construction-id-pushout (succ-ℕ n))))) b

  span-diagram-path-to-a :
    domain-span-diagram 𝒮 → ℕ →
    span-diagram
      ( l1 ⊔ l2 ⊔ l3)
      ( l1 ⊔ l2 ⊔ l3)
      ( l1 ⊔ l2 ⊔ l3)
  span-diagram-path-to-a a n =
    pr2 (pr2 (pr2 (pr2 (stage-zigzag-construction-id-pushout (succ-ℕ n))))) a

  Path-to-b : codomain-span-diagram 𝒮 → ℕ → UU (l1 ⊔ l2 ⊔ l3)
  Path-to-b b n = pr1 (stage-zigzag-construction-id-pushout n) b

  Path-to-a : domain-span-diagram 𝒮 → ℕ → UU (l1 ⊔ l2 ⊔ l3)
  Path-to-a a n = pr1 (pr2 (stage-zigzag-construction-id-pushout n)) a

  inl-Path-to-b :
    (b : codomain-span-diagram 𝒮) (n : ℕ) → Path-to-b b n → Path-to-b b (succ-ℕ n)
  inl-Path-to-b b n =
    inl-standard-pushout
      ( span-diagram-path-to-b b n)

  inl-Path-to-a :
    (a : domain-span-diagram 𝒮) (n : ℕ) → Path-to-a a n → Path-to-a a (succ-ℕ n)
  inl-Path-to-a a n =
    inl-standard-pushout
      ( span-diagram-path-to-a a n)

  concat-inv-s :
    (s : spanning-type-span-diagram 𝒮) →
    (n : ℕ) →
    Path-to-b (right-map-span-diagram 𝒮 s) n →
    Path-to-a (left-map-span-diagram 𝒮 s) n
  concat-inv-s s n = pr1 (pr2 (pr2 (stage-zigzag-construction-id-pushout n))) s

  concat-s :
    (s : spanning-type-span-diagram 𝒮) →
    (n : ℕ) →
    Path-to-a (left-map-span-diagram 𝒮 s) n →
    Path-to-b (right-map-span-diagram 𝒮 s) (succ-ℕ n)
  concat-s s n p =
    inr-standard-pushout
      ( span-diagram-path-to-b (right-map-span-diagram 𝒮 s) n)
      ( s , refl , p)

  right-sequential-diagram-zigzag-id-pushout :
    codomain-span-diagram 𝒮 →
    sequential-diagram (l1 ⊔ l2 ⊔ l3)
  pr1 (right-sequential-diagram-zigzag-id-pushout b) = Path-to-b b
  pr2 (right-sequential-diagram-zigzag-id-pushout b) = inl-Path-to-b b

  left-sequential-diagram-zigzag-id-pushout :
    domain-span-diagram 𝒮 →
    sequential-diagram (l1 ⊔ l2 ⊔ l3)
  pr1 (left-sequential-diagram-zigzag-id-pushout a) = Path-to-a a
  pr2 (left-sequential-diagram-zigzag-id-pushout a) = inl-Path-to-a a

  zigzag-sequential-diagram-zigzag-id-pushout :
    (s : spanning-type-span-diagram 𝒮) →
    zigzag-sequential-diagram
      ( left-sequential-diagram-zigzag-id-pushout
        ( left-map-span-diagram 𝒮 s))
      ( shift-once-sequential-diagram
        ( right-sequential-diagram-zigzag-id-pushout
          ( right-map-span-diagram 𝒮 s)))
  pr1 (zigzag-sequential-diagram-zigzag-id-pushout s) =
    concat-s s
  pr1 (pr2 (zigzag-sequential-diagram-zigzag-id-pushout s)) n =
    concat-inv-s s (succ-ℕ n)
  pr1 (pr2 (pr2 (zigzag-sequential-diagram-zigzag-id-pushout s))) n p =
    glue-standard-pushout
      ( span-diagram-path-to-a (left-map-span-diagram 𝒮 s) n)
      ( s , refl , p)
  pr2 (pr2 (pr2 (zigzag-sequential-diagram-zigzag-id-pushout s))) n p =
    glue-standard-pushout
      ( span-diagram-path-to-b (right-map-span-diagram 𝒮 s) (succ-ℕ n))
      ( s , refl , p)

  left-id-pushout : domain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3)
  left-id-pushout a =
    standard-sequential-colimit (left-sequential-diagram-zigzag-id-pushout a)

  refl-id-pushout : left-id-pushout a₀
  refl-id-pushout =
    map-cocone-standard-sequential-colimit 0 (map-raise refl)

  right-id-pushout : codomain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3)
  right-id-pushout b =
    standard-sequential-colimit (right-sequential-diagram-zigzag-id-pushout b)

  equiv-id-pushout :
    (s : spanning-type-span-diagram 𝒮) →
    left-id-pushout (left-map-span-diagram 𝒮 s) ≃
    right-id-pushout (right-map-span-diagram 𝒮 s)
  equiv-id-pushout s =
    equiv-colimit-zigzag-sequential-diagram _ _
      ( up-standard-sequential-colimit)
      ( up-shift-cocone-sequential-diagram 1 up-standard-sequential-colimit)
      ( zigzag-sequential-diagram-zigzag-id-pushout s)

  concat-inv-s-inf :
    (s : spanning-type-span-diagram 𝒮) →
    right-id-pushout (right-map-span-diagram 𝒮 s) →
    left-id-pushout (left-map-span-diagram 𝒮 s)
  concat-inv-s-inf s =
    map-inv-equiv (equiv-id-pushout s)

  concat-s-inf :
    (s : spanning-type-span-diagram 𝒮) →
    left-id-pushout (left-map-span-diagram 𝒮 s) →
    right-id-pushout (right-map-span-diagram 𝒮 s)
  concat-s-inf s =
    map-equiv (equiv-id-pushout s)

  descent-data-zigzag-id-pushout : descent-data-pushout 𝒮 (l1 ⊔ l2 ⊔ l3)
  pr1 descent-data-zigzag-id-pushout = left-id-pushout
  pr1 (pr2 descent-data-zigzag-id-pushout) = right-id-pushout
  pr2 (pr2 descent-data-zigzag-id-pushout) = equiv-id-pushout
```

## Theorem

### TODO

```agda
nat-lemma :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  {P : A → UU l3} {Q : B → UU l4}
  (f : A → B) (h : (a : A) → P a → Q (f a))
  {x y : A} {p : x ＝ y}
  {q : f x ＝ f y} (α : ap f p ＝ q) →
  coherence-square-maps
    ( tr P p)
    ( h x)
    ( h y)
    ( tr Q q)
nat-lemma f h {p = p} refl x = substitution-law-tr _ f p ∙ inv (preserves-tr h p x)

apd-lemma :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  (f : (a : A) → B a) (g : (a : A) → B a → C a) {x y : A} (p : x ＝ y) →
  apd (λ a → g a (f a)) p ＝ inv (preserves-tr g p (f x)) ∙ ap (g y) (apd f p)
apd-lemma f g refl = refl

module _
  {l1 l2 l3 l4 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (up-c : universal-property-pushout _ _ c)
  (a₀ : domain-span-diagram 𝒮)
  where

  module _
    {l5 : Level}
    (R : descent-data-pushout
      ( span-diagram-flattening-descent-data-pushout
        ( descent-data-zigzag-id-pushout 𝒮 a₀))
      ( l5))
    (r₀ : left-family-descent-data-pushout R (a₀ , refl-id-pushout 𝒮 a₀))
    where

    -- type-stage-ind-singleton-zigzag-id-pushout : ℕ → UU (l1 ⊔ l2 ⊔ l3 ⊔ l5)
    -- type-stage-ind-singleton-zigzag-id-pushout n =
    --   Σ ( (b : codomain-span-diagram 𝒮) (p : Path-to-b 𝒮 a₀ b n) →
    --       right-family-descent-data-pushout R
    --         ( b , map-cocone-standard-sequential-colimit n p))
    --     ( λ tB →
    --       Σ ( (a : domain-span-diagram 𝒮) (p : Path-to-a 𝒮 a₀ a n) →
    --           left-family-descent-data-pushout R
    --             ( a , map-cocone-standard-sequential-colimit n p))
    --         ( λ tA →
    --           rec-ℕ
    --             ( raise-unit (l1 ⊔ l2 ⊔ l3 ⊔ l5))
    --             ( λ n' _ →
    --               ( (b : codomain-span-diagram 𝒮) →
    --                 dependent-cocone-span-diagram
    --                   ( cocone-pushout-span-diagram
    --                     ( span-diagram-path-to-b 𝒮 a₀ b n'))
    --                   ( λ p →
    --                     right-family-descent-data-pushout R
    --                       ( b , map-cocone-standard-sequential-colimit (succ-ℕ n') p))) ×
    --               ( (a : domain-span-diagram 𝒮) →
    --                 dependent-cocone-span-diagram
    --                   ( cocone-pushout-span-diagram
    --                     ( span-diagram-path-to-a 𝒮 a₀ a n'))
    --                   ( λ p →
    --                     left-family-descent-data-pushout R
    --                       ( a , map-cocone-standard-sequential-colimit (succ-ℕ n') p))))
    --             ( n)))

    private
      CB :
        (s : spanning-type-span-diagram 𝒮) →
        (n : ℕ) →
        (p : Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) n) →
        concat-s-inf 𝒮 a₀ s
          ( map-cocone-standard-sequential-colimit n p) ＝
        map-cocone-standard-sequential-colimit (succ-ℕ n)
          ( concat-s 𝒮 a₀ s n p)
      CB s =
        htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
          ( up-standard-sequential-colimit)
          ( shift-once-cocone-sequential-diagram
            ( cocone-standard-sequential-colimit
              ( right-sequential-diagram-zigzag-id-pushout 𝒮 a₀ (right-map-span-diagram 𝒮 s))))
          ( hom-diagram-zigzag-sequential-diagram
            ( zigzag-sequential-diagram-zigzag-id-pushout 𝒮 a₀ s))

      foo :
        (s : spanning-type-span-diagram 𝒮) →
        (n : ℕ) →
        (p : Path-to-b 𝒮 a₀ (right-map-span-diagram 𝒮 s) (succ-ℕ n)) →
        right-family-descent-data-pushout R
          ( right-map-span-diagram 𝒮 s , map-cocone-standard-sequential-colimit (succ-ℕ n) p) →
        right-family-descent-data-pushout R
          ( right-map-span-diagram 𝒮 s ,
            concat-s-inf 𝒮 a₀ s (map-cocone-standard-sequential-colimit (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p)))
      foo s n p =
        ( tr
          ( ev-pair (right-family-descent-data-pushout R) (right-map-span-diagram 𝒮 s))
          ( inv (CB s (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p)))) ∘
        ( tr
          ( λ p →
            right-family-descent-data-pushout R
              ( right-map-span-diagram 𝒮 s , map-cocone-standard-sequential-colimit (succ-ℕ (succ-ℕ n)) p))
          ( glue-pushout _ _ (s , refl , p))) ∘
        ( tr
          ( ev-pair (right-family-descent-data-pushout R) (right-map-span-diagram 𝒮 s))
          ( coherence-cocone-standard-sequential-colimit (succ-ℕ n) p))

    coh-dep-cocone-a :
      (s : spanning-type-span-diagram 𝒮) (n : ℕ) →
      (p : Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) n) →
      coherence-square-maps
        ( ( tr
            ( λ p →
              left-family-descent-data-pushout R
                ( left-map-span-diagram 𝒮 s ,
                  map-cocone-standard-sequential-colimit (succ-ℕ n) p))
            ( glue-pushout _ _ (s , refl , p))) ∘
          ( tr
            ( ev-pair
              ( left-family-descent-data-pushout R)
              ( left-map-span-diagram 𝒮 s))
            ( coherence-cocone-standard-sequential-colimit n p)))
        ( map-family-descent-data-pushout R
          ( s , map-cocone-standard-sequential-colimit n p))
        ( map-family-descent-data-pushout R
          ( s ,
            map-cocone-standard-sequential-colimit (succ-ℕ n)
              ( concat-inv-s 𝒮 a₀ s (succ-ℕ n) ( concat-s 𝒮 a₀ s n p))))
        ( ( tr
            ( ev-pair
              ( right-family-descent-data-pushout R)
              ( right-map-span-diagram 𝒮 s))
            ( inv (CB s (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) (concat-s 𝒮 a₀ s n p))))) ∘
          ( tr
            ( λ p →
              right-family-descent-data-pushout R
                ( right-map-span-diagram 𝒮 s ,
                  map-cocone-standard-sequential-colimit (succ-ℕ (succ-ℕ n)) p))
            ( glue-pushout _ _ (s , refl , concat-s 𝒮 a₀ s n p))) ∘
          ( tr
            ( ev-pair
              ( right-family-descent-data-pushout R)
              ( right-map-span-diagram 𝒮 s))
            ( coherence-cocone-standard-sequential-colimit (succ-ℕ n) (concat-s 𝒮 a₀ s n p))) ∘
          ( tr
            ( ev-pair
              ( right-family-descent-data-pushout R)
              ( right-map-span-diagram 𝒮 s))
            ( CB s n p)))
    coh-dep-cocone-a s n p =
      ( ( inv-htpy
          ( ( tr-concat _ _) ∙h
            ( ( tr _ _) ·l
              ( ( tr-concat _ _) ∙h
                ( horizontal-concat-htpy
                  ( λ _ → substitution-law-tr _ _ _)
                  ( tr-concat _ _)))))) ·r
        ( map-family-descent-data-pushout R
          ( s , map-cocone-standard-sequential-colimit n p))) ∙h
      ( nat-lemma
          ( concat-s-inf 𝒮 a₀ s)
          ( ev-pair (map-family-descent-data-pushout R) s)
          ( [i] p)) ∙h
      ( ( map-family-descent-data-pushout R
          ( s ,
            map-cocone-standard-sequential-colimit
              ( succ-ℕ n)
              ( concat-inv-s 𝒮 a₀ s
                ( succ-ℕ n)
                ( concat-s 𝒮 a₀ s n p)))) ·l
        ( ( tr-concat _ _) ∙h
          ( λ q → substitution-law-tr _ _ _)))
      where
      [i] :
        ( ( concat-s-inf 𝒮 a₀ s) ·l
          ( ( coherence-cocone-standard-sequential-colimit n) ∙h
            ( ( map-cocone-standard-sequential-colimit
              { A =
                left-sequential-diagram-zigzag-id-pushout 𝒮 a₀
                  ( left-map-span-diagram 𝒮 s)}
              ( succ-ℕ n)) ·l
            ( λ p → glue-pushout _ _ (s , refl , p))))) ~
        ( ( CB s n) ∙h
          ( ( coherence-cocone-standard-sequential-colimit (succ-ℕ n)) ·r
              ( concat-s 𝒮 a₀ s n)) ∙h
          ( ( map-cocone-standard-sequential-colimit
              { A =
                right-sequential-diagram-zigzag-id-pushout 𝒮 a₀
                  ( right-map-span-diagram 𝒮 s)}
              ( succ-ℕ (succ-ℕ n))) ·l
            ( λ p → glue-pushout _ _ ( s , refl , concat-s 𝒮 a₀ s n p))) ∙h
          ( ( inv-htpy (CB s (succ-ℕ n))) ·r
            ( concat-inv-s 𝒮 a₀ s (succ-ℕ n) ∘ concat-s 𝒮 a₀ s n)))
      [i] =
        ( distributive-left-whisker-comp-concat _ _ _) ∙h
        ( right-transpose-htpy-concat _ _ _
          ( ( left-whisker-concat-coherence-square-homotopies _ _ _ _ _
              ( λ p →
                inv
                  ( nat-coherence-square-maps _ _ _ _
                    ( CB s (succ-ℕ n))
                    ( glue-pushout _ _ (s , refl , p))))) ∙h
            ( map-inv-equiv
              ( equiv-right-transpose-htpy-concat _ _ _)
              ( ( coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
                  ( up-standard-sequential-colimit)
                  ( shift-once-cocone-sequential-diagram
                    ( cocone-standard-sequential-colimit
                      ( right-sequential-diagram-zigzag-id-pushout 𝒮 a₀
                        ( right-map-span-diagram 𝒮 s))))
                  ( hom-diagram-zigzag-sequential-diagram
                    ( zigzag-sequential-diagram-zigzag-id-pushout 𝒮 a₀ s))
                  ( n)) ∙h
                ( ap-concat-htpy
                  ( CB s n)
                  ( ( ap-concat-htpy _
                      ( ( distributive-left-whisker-comp-concat
                          ( map-cocone-standard-sequential-colimit
                            { A =
                              right-sequential-diagram-zigzag-id-pushout 𝒮 a₀
                                ( right-map-span-diagram 𝒮 s)}
                            ( succ-ℕ (succ-ℕ n)))
                          ( _)
                          ( _)) ∙h
                        ( ap-concat-htpy _
                          ( ( left-whisker-comp² _
                              ( left-whisker-inv-htpy _ _)) ∙h
                            ( left-whisker-inv-htpy _ _))))) ∙h
                    ( inv-htpy-assoc-htpy _ _ _))) ∙h
                ( inv-htpy-assoc-htpy _ _ _))))) ∙h
        ( ap-concat-htpy' _
          ( inv-htpy-assoc-htpy _ _ _))


    -- TODO: Explore omitting vertical-map-dependent-cocone
    stages-cocones' :
      (n : ℕ) →
      Σ ( (b : codomain-span-diagram 𝒮) →
          dependent-cocone-span-diagram
            ( cocone-pushout-span-diagram
              ( span-diagram-path-to-b 𝒮 a₀ b n))
            ( λ p →
              right-family-descent-data-pushout R
                ( b , map-cocone-standard-sequential-colimit (succ-ℕ n) p)))
        ( λ dep-cocone-b →
          Σ ( (a : domain-span-diagram 𝒮) →
              dependent-cocone-span-diagram
                ( cocone-pushout-span-diagram
                  ( span-diagram-path-to-a 𝒮 a₀ a n))
                ( λ p →
                  left-family-descent-data-pushout R
                    ( a , map-cocone-standard-sequential-colimit (succ-ℕ n) p)))
            ( λ dep-cocone-a →
              (s : spanning-type-span-diagram 𝒮) →
              (p : Path-to-b 𝒮 a₀ (right-map-span-diagram 𝒮 s) (succ-ℕ n)) →
              vertical-map-dependent-cocone _ _ _ _
                ( dep-cocone-a (left-map-span-diagram 𝒮 s))
                ( s , refl , p) ＝
              inv-map-family-descent-data-pushout R
                ( s , map-cocone-standard-sequential-colimit (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p))
                ( foo s n p (dependent-cogap _ _ (dep-cocone-b (right-map-span-diagram 𝒮 s)) p))))
    stages-cocones' zero-ℕ =
      dep-cocone-b ,
      dep-cocone-a ,
      λ s p → refl
      where
      dep-cocone-b :
        (b : codomain-span-diagram 𝒮) →
        dependent-cocone-span-diagram
          ( cocone-pushout-span-diagram (span-diagram-path-to-b 𝒮 a₀ b 0))
          ( λ p →
            right-family-descent-data-pushout R
              ( b , map-cocone-standard-sequential-colimit 1 p))
      pr1 (dep-cocone-b b) (map-raise ())
      pr1 (pr2 (dep-cocone-b ._)) (s , refl , map-raise refl) =
        tr
          ( ev-pair
            ( right-family-descent-data-pushout R)
            ( right-map-span-diagram 𝒮 s))
          ( CB s 0 (map-raise refl))
          ( map-family-descent-data-pushout R
            ( s , map-cocone-standard-sequential-colimit 0 (map-raise refl))
            ( r₀))
      pr2 (pr2 (dep-cocone-b ._)) (s , refl , map-raise ())
      dep-cocone-a :
        (a : domain-span-diagram 𝒮) →
        dependent-cocone-span-diagram
          ( cocone-pushout-span-diagram (span-diagram-path-to-a 𝒮 a₀ a 0))
          ( λ p →
            left-family-descent-data-pushout R
              ( a , map-cocone-standard-sequential-colimit 1 p))
      pr1 (dep-cocone-a .a₀) (map-raise refl) =
        tr
          ( ev-pair (left-family-descent-data-pushout R) a₀)
          ( coherence-cocone-standard-sequential-colimit 0 (map-raise refl))
          ( r₀)
      pr1 (pr2 (dep-cocone-a a)) (s , refl , p) =
        inv-map-family-descent-data-pushout R
          ( s , map-cocone-standard-sequential-colimit 1 (concat-inv-s 𝒮 a₀ s 1 p))
          ( foo s 0 p (dependent-cogap _ _ (dep-cocone-b (right-map-span-diagram 𝒮 s)) p))
      pr2 (pr2 (dep-cocone-a .a₀)) (s , refl , map-raise refl) =
        map-eq-transpose-equiv
          ( equiv-family-descent-data-pushout R
            ( s ,
              map-cocone-standard-sequential-colimit 1
                ( concat-inv-s 𝒮 a₀ s 1 (concat-s 𝒮 a₀ s 0 (map-raise refl)))))
          ( inv
            ( ( ap
                ( foo s 0 (concat-s 𝒮 a₀ s 0 (map-raise refl)))
                ( compute-inr-dependent-cogap _ _
                  ( dep-cocone-b (right-map-span-diagram 𝒮 s))
                  (s , refl , map-raise refl))) ∙
              ( coh-dep-cocone-a s 0 (map-raise refl) r₀)))
    stages-cocones' (succ-ℕ n) =
      dep-cocone-b ,
      dep-cocone-a ,
      λ s p → refl
      where
      dep-cocone-b :
        (b : codomain-span-diagram 𝒮) →
        dependent-cocone-span-diagram
          ( cocone-pushout-span-diagram (span-diagram-path-to-b 𝒮 a₀ b (succ-ℕ n)))
          ( λ p →
            right-family-descent-data-pushout R
              ( b , map-cocone-standard-sequential-colimit (succ-ℕ (succ-ℕ n)) p))
      pr1 (dep-cocone-b b) p =
        tr
          ( ev-pair (right-family-descent-data-pushout R) b)
          ( coherence-cocone-standard-sequential-colimit (succ-ℕ n) p)
          ( dependent-cogap _ _ (pr1 (stages-cocones' n) b) p)
      pr1 (pr2 (dep-cocone-b b)) (s , refl , p) =
        tr
          ( ev-pair
            ( right-family-descent-data-pushout R)
            ( right-map-span-diagram 𝒮 s))
          ( CB s (succ-ℕ n) p)
          ( map-family-descent-data-pushout R
            ( s , map-cocone-standard-sequential-colimit (succ-ℕ n) p)
            ( dependent-cogap _ _ (pr1 (pr2 (stages-cocones' n)) (left-map-span-diagram 𝒮 s)) p))
      pr2 (pr2 (dep-cocone-b b)) (s , refl , p) =
        inv
          ( ( ap
              ( λ q →
                tr
                  ( ev-pair
                    ( right-family-descent-data-pushout R)
                    ( right-map-span-diagram 𝒮 s))
                  ( CB s (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p))
                  ( map-family-descent-data-pushout R
                    ( s ,
                      ( map-cocone-standard-sequential-colimit
                        ( succ-ℕ n)
                        ( concat-inv-s 𝒮 a₀ s (succ-ℕ n) p)))
                    ( q)))
              ( ( compute-inr-dependent-cogap _ _
                  ( pr1 (pr2 (stages-cocones' n)) (left-map-span-diagram 𝒮 s))
                  ( s , refl , p)) ∙
                ( pr2 (pr2 (stages-cocones' n)) s p))) ∙
            ( ap
              ( tr
                ( ev-pair
                  ( right-family-descent-data-pushout R)
                  ( right-map-span-diagram 𝒮 s))
                ( CB s (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p)))
              ( is-section-map-inv-equiv
                ( equiv-family-descent-data-pushout R
                  ( s , map-cocone-standard-sequential-colimit (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p)))
                ( foo s n p (dependent-cogap _ _
                  ( pr1 (stages-cocones' n) (right-map-span-diagram 𝒮 s)) p)))) ∙
            ( is-section-map-inv-equiv
              ( equiv-tr
                ( ev-pair (right-family-descent-data-pushout R) (right-map-span-diagram 𝒮 s))
                ( CB s (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p)))
              ( _)))
      dep-cocone-a :
        (a : domain-span-diagram 𝒮) →
        dependent-cocone-span-diagram
          ( cocone-pushout-span-diagram (span-diagram-path-to-a 𝒮 a₀ a (succ-ℕ n)))
          ( λ p →
            left-family-descent-data-pushout R
              ( a , map-cocone-standard-sequential-colimit (succ-ℕ (succ-ℕ n)) p))
      pr1 (dep-cocone-a a) p =
        tr
          ( ev-pair (left-family-descent-data-pushout R) a)
          ( coherence-cocone-standard-sequential-colimit (succ-ℕ n) p)
          ( dependent-cogap _ _ (pr1 (pr2 (stages-cocones' n)) a) p)
      pr1 (pr2 (dep-cocone-a a)) (s , refl , p) =
        inv-map-family-descent-data-pushout R
          ( s , map-cocone-standard-sequential-colimit (succ-ℕ (succ-ℕ n)) (concat-inv-s 𝒮 a₀ s (succ-ℕ (succ-ℕ n)) p))
          ( foo s (succ-ℕ n) p (dependent-cogap _ _ (dep-cocone-b (right-map-span-diagram 𝒮 s)) p))
      pr2 (pr2 (dep-cocone-a a)) (s , refl , p) =
        map-eq-transpose-equiv
          ( equiv-family-descent-data-pushout R
            ( s ,
              map-cocone-standard-sequential-colimit
                ( succ-ℕ (succ-ℕ n))
                ( concat-inv-s 𝒮 a₀ s
                  ( succ-ℕ (succ-ℕ n))
                  ( concat-s 𝒮 a₀ s (succ-ℕ n) p))))
          ( inv
            ( ( ap
                ( foo s (succ-ℕ n) (concat-s 𝒮 a₀ s (succ-ℕ n) p))
                ( compute-inr-dependent-cogap _ _
                  ( dep-cocone-b (right-map-span-diagram 𝒮 s))
                  ( s , refl , p))) ∙
              ( coh-dep-cocone-a s
                ( succ-ℕ n)
                ( p)
                ( dependent-cogap _ _
                  (pr1 (pr2 (stages-cocones' n)) (left-map-span-diagram 𝒮 s)) p))))

    tA :
      (a : domain-span-diagram 𝒮) (n : ℕ) (p : Path-to-a 𝒮 a₀ a n) →
      left-family-descent-data-pushout R
        ( a , map-cocone-standard-sequential-colimit n p)
    tA .a₀ zero-ℕ (map-raise refl) = r₀
    tA a (succ-ℕ n) = dependent-cogap _ _ (pr1 (pr2 (stages-cocones' n)) a)

    tB :
      (b : codomain-span-diagram 𝒮) (n : ℕ) (p : Path-to-b 𝒮 a₀ b n) →
      right-family-descent-data-pushout R
        ( b , map-cocone-standard-sequential-colimit n p)
    tB b zero-ℕ (map-raise ())
    tB b (succ-ℕ n) = dependent-cogap _ _ (pr1 (stages-cocones' n) b)

    ind-singleton-zigzag-id-pushout' : section-descent-data-pushout R
    pr1 ind-singleton-zigzag-id-pushout' (a , p) =
      dependent-cogap-standard-sequential-colimit
        ( tA a , KA)
        ( p)
      where
      KA :
        (n : ℕ) (p : Path-to-a 𝒮 a₀ a n) →
        dependent-identification
          ( ev-pair (left-family-descent-data-pushout R) a)
          ( coherence-cocone-standard-sequential-colimit n p)
          ( tA a n p)
          ( tA a (succ-ℕ n) (inl-Path-to-a 𝒮 a₀ a n p))
      KA zero-ℕ (map-raise refl) =
        inv
          ( compute-inl-dependent-cogap _ _
            ( pr1 (pr2 (stages-cocones' 0)) a)
            ( map-raise refl))
      KA (succ-ℕ n) p =
        inv
          ( compute-inl-dependent-cogap _ _
            ( pr1 (pr2 (stages-cocones' (succ-ℕ n))) a)
            ( p))
    pr1 (pr2 ind-singleton-zigzag-id-pushout') (b , p) =
      dependent-cogap-standard-sequential-colimit
        ( tB b , KB)
        ( p)
      where
      KB :
        (n : ℕ) (p : Path-to-b 𝒮 a₀ b n) →
        dependent-identification
          ( ev-pair (right-family-descent-data-pushout R) b)
          ( coherence-cocone-standard-sequential-colimit n p)
          ( tB b n p)
          ( tB b (succ-ℕ n) (inl-Path-to-b 𝒮 a₀ b n p))
      KB zero-ℕ (map-raise ())
      KB (succ-ℕ n) p =
        inv
          ( compute-inl-dependent-cogap _ _
            ( pr1 (stages-cocones' (succ-ℕ n)) b)
            ( p))
    pr2 (pr2 ind-singleton-zigzag-id-pushout') (s , p) =
      dependent-cogap-standard-sequential-colimit
        ( tS , {!!})
        ( p)
      where
      [i] :
        (n : ℕ) (p : Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) n) →
        tr
          ( ev-pair
            ( right-family-descent-data-pushout R)
            ( right-map-span-diagram 𝒮 s))
          ( CB s n p)
          ( map-family-descent-data-pushout R
            ( s , map-cocone-standard-sequential-colimit n p)
            ( tA (left-map-span-diagram 𝒮 s) n p)) ＝
        tB (right-map-span-diagram 𝒮 s) (succ-ℕ n) (concat-s 𝒮 a₀ s n p)
      [i] zero-ℕ (map-raise refl) = inv (compute-inr-dependent-cogap _ _ _ _)
      [i] (succ-ℕ n) p = inv (compute-inr-dependent-cogap _ _ _ _)
      tS :
        (n : ℕ) (p : Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) n) →
        map-family-descent-data-pushout R
          ( s , map-cocone-standard-sequential-colimit n p)
          ( pr1
            ( ind-singleton-zigzag-id-pushout')
            ( left-map-span-diagram 𝒮 s ,
              map-cocone-standard-sequential-colimit n p)) ＝
        pr1
          ( pr2 ind-singleton-zigzag-id-pushout')
          ( right-map-span-diagram 𝒮 s ,
            concat-s-inf 𝒮 a₀ s (map-cocone-standard-sequential-colimit n p))
      tS n p =
        ( ap
          ( map-family-descent-data-pushout R
            ( s , map-cocone-standard-sequential-colimit n p))
          ( compute-incl-dependent-cogap-standard-sequential-colimit _ n p)) ∙
        ( map-equiv
          ( inv-equiv-ap-emb
            ( emb-equiv
              ( equiv-tr
                ( ev-pair
                  ( right-family-descent-data-pushout R)
                  ( right-map-span-diagram 𝒮 s))
                ( CB s n p))))
          ( [i] n p ∙
            inv
              ( ( apd
                  ( dependent-cogap-standard-sequential-colimit (tB (right-map-span-diagram 𝒮 s) , _))
                  ( CB s n p)) ∙
                ( compute-incl-dependent-cogap-standard-sequential-colimit _ (succ-ℕ n) _))))
      KS :
        (n : ℕ) (p : Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) n) →
        tr
          ( λ p →
            map-family-descent-data-pushout R
              ( s , p)
              ( pr1
                ( ind-singleton-zigzag-id-pushout')
                ( left-map-span-diagram 𝒮 s , p)) ＝
            pr1 (pr2 ind-singleton-zigzag-id-pushout') (right-map-span-diagram 𝒮 s , concat-s-inf 𝒮 a₀ s p))
          ( coherence-cocone-standard-sequential-colimit n p)
          ( tS n p) ＝
        tS (succ-ℕ n) (inl-Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) n p)
      KS zero-ℕ (map-raise refl) =
        map-compute-dependent-identification-eq-value _ _
          ( coherence-cocone-standard-sequential-colimit 0 (map-raise refl))
          ( _)
          ( _)
          ( {!!})
      KS (succ-ℕ n) p = {!!}

  is-identity-system-zigzag-id-pushout :
    is-identity-system-descent-data-pushout
      ( descent-data-zigzag-id-pushout 𝒮 a₀)
      ( refl-id-pushout 𝒮 a₀)
  is-identity-system-zigzag-id-pushout =
    is-identity-system-descent-data-pushout-ind-singleton up-c
      ( descent-data-zigzag-id-pushout 𝒮 a₀)
      ( refl-id-pushout 𝒮 a₀)
      ( ind-singleton-zigzag-id-pushout')
```
