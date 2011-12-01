package

/**
 * Created by IntelliJ IDEA.
 * User: Uri
 * Date: 01/12/11
 * Time: 16:02
 * To change this template use File | Settings | File Templates.
 */

class Food;
class Grass extends Food
class Meat extends Food

abstract class Animal {
  type F <: Food
  def eat(f:F)
}

class Cow extends Animal{
  type F = Grass
  def eat(f : F) = {}
}

class Lion extends Animal{
  type F = Meat
  def eat(f : F) = {}
}

object ttt{
  def f = {
    val cow = new Cow
    val lion = new Lion
    val grass = new Grass
    val meat = new Meat

    lion.eat(meat)
    cow.eat(grass)

    val a1 : Animal = cow
    val a2 : Animal = lion
  }
  def g(a : Animal, f : a.F) = {

  }
}