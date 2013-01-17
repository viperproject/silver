package semper.sil.testing

import java.nio.file.Paths

/** The default test suite to be used in Semper projects.
  */
abstract class DefaultSilSuite extends SilSuite {

  override def baseDirectory = {
    val rootUrl = getClass.getResource("")
    Paths.get(rootUrl.toURI).getParent.getParent
  }
}
