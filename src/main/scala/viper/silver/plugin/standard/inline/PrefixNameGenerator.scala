package viper.silver.plugin.standard.inline

import viper.silver.utility.SilNameGenerator

class PrefixNameGenerator(val prefix: String) extends SilNameGenerator {
  override def createUnique(s: String): String =  {
    super.createUnique(s"_$prefix$$$s")
  }
}
