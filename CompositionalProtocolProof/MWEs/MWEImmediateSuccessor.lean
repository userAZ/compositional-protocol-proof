import Mathlib

inductive Fruit
| apple : Fruit
| banana : Fruit
| pear : Fruit

structure FruitNat where
  fruit : Fruit
  nat : Nat

def FruitNat.natLt (x y : FruitNat) : Prop := x.nat < y.nat
