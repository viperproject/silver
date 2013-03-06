package semper.sil.utility

import java.util.regex.Pattern

/**
 * A simple collection of utility methods for dealing with paths and environment variables.
 *
 * @author Stefan Heule
 */
object Paths {

  /**
   * Resolve any environment variables that occur in a given string.  The syntax to mention environment
   * variables is `${ENV}`.  Environment variables that have not been found are not replaced.
   */
  def resolveEnvVars(path: String): String = {
    val matcher = "\\$\\{([^\\}]+)\\}".r.pattern.matcher(path)
    var res = path
    while(matcher.find()) {
      val env = matcher.group(1)
      val envVal = System.getenv(env)
      if (envVal != null)
        res = res.replace(matcher.group(0), envVal)
    }
    res
  }
}
