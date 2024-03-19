package viper.silver.ast.utility

import java.nio.file.Path
import scala.io.Source
import scala.util.{Using, Try}

trait FileLoader {
  def loadContent(path: Path): Try[String]
}

trait DiskLoader extends FileLoader {
  override def loadContent(path: Path): Try[String] = {
    Using(Source.fromFile(path.toFile()))(_.mkString)
  }
}

object DiskLoader extends DiskLoader
