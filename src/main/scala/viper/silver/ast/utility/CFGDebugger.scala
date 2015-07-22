package viper.silver.ast.utility

import java.nio.file.{StandardOpenOption, Files, Paths}

import viper.silver.ast.Block

object CFGDebugger {
  var count = -1
  val pathToOutput = "..\\silver\\src\\test\\resources\\all\\_debug\\"
  val logFileName = "_cfgDebug.log"

  def clearLog = Files.deleteIfExists(Paths.get(pathToOutput + logFileName))

  def println(s:String):Unit = {
    val path = Paths.get(pathToOutput + logFileName)

    try{
      Files.createDirectories(path.getParent)
      Files.write(path, s.getBytes,
        StandardOpenOption.CREATE,
        StandardOpenOption.APPEND)
    }catch{
      case _:Exception => println("log write failed")
    }
  }

  def print(b:Block):Unit = this.print(b.toDot)

  protected def print(s:String):Unit = {
    count = count + 1

    try{
      val filename = f"debugCFG[$count%06d].dot"
      val path = Paths.get(pathToOutput + filename)

      Files.createDirectories(path.getParent)
      Files.write(path, s.getBytes,
        StandardOpenOption.CREATE,
        StandardOpenOption.TRUNCATE_EXISTING)
    }catch{
      case _:Exception => println("failed to write")
    }
  }
}

