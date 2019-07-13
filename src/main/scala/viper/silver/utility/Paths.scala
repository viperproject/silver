// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.utility

import java.io.File
import java.net.{URI, URL}
import java.nio.file.{FileSystem, FileSystems, Path}

import scala.collection.JavaConverters._

/**
  * A collection of utility methods for dealing with paths and environment variables.
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



  private var openFileSystems: Seq[FileSystem] = Seq()

  addShutdownHookForOpenFileSystems()

  /**
    * Creates a path from the given URL, which, for example, could have been
    * obtained by calling [[java.lang.ClassLoader]]. The current implementation
    * can handle URLs that point into the normal file system (file:...) or
    * into a jar file (jar:...).
    *
    * Based on code taken from http://stackoverflow.com/a/15718001/491216.
    *
    * @param resource The URL to turn into a path.
    * @return The path obtained from the URL.
    */
  def pathFromResource(resource: URL): Path = {
    assert(resource != null, "Resource URL must not be null")

    val uri = resource.toURI

    uri.getScheme match {
      case "file" => java.nio.file.Paths.get(uri)

      case "jar" =>
        val uriStr = uri.toString
        val separator = uriStr.indexOf("!/")
        val entryName = uriStr.substring(separator + 2)
        val fileURI = URI.create(uriStr.substring(0, separator))

        // 2013-05-03 Malte:
        // The following bit of code is quite nasty, but I wasn't able to get anything less
        // nasty to work reliably. There are two main problems:
        //
        // 1. It is not obvious when to close the file system, because several components of
        //    our tool chain keep references to path objects that in turn have references
        //    to their underlying file system. If these path objects are used (not all usages
        //    seem dangerous, though) after the underlying file system has been closed, an
        //    exception is thrown.
        //
        // 2. If the test suite is executed from an Sbt prompt then the shutdown hook of
        //    the runtime environment doesn't seem to fire and the file systems don't seem
        //    to be closed. Thus, if the tests are executed again without existing the
        //    Sbt prompt, FileSystemAlreadyExistsExceptions can be thrown because some
        //    file systems are still open.
        //
        // The list of open file systems (openFileSystems) unfortunately doesn't seem to
        // survive, otherwise it might have been possible to maintain a map from file URI
        // to file system and only create a new file system if there is no map entry for
        // the given file URI yet.
        //
        // I also tried to use a finalizer method instead of the shutdown hook, but the
        // finalizer also doesn't seem to be called if the Sbt prompt is not existed.

        var fs: FileSystem = null

        try {
          fs = FileSystems.newFileSystem(fileURI, Map[String, Object]().asJava)
          openFileSystems = fs +: openFileSystems
        } catch {
          case e: java.nio.file.FileSystemAlreadyExistsException =>
            fs = FileSystems.getFileSystem(fileURI)
            assert(fs.isOpen, "The reused file system is expected to still be open")
        } finally {
          assert(fs != null, s"Could not get hold of a file system for $fileURI (from $uriStr)")
        }

        fs.getPath(entryName)

      case other => sys.error(s"Resource $uri of scheme $other is not supported.")
    }
  }

  /** Closes all open file systems stored in `openFileSystems`. */
  private def addShutdownHookForOpenFileSystems() {
    Runtime.getRuntime.addShutdownHook(new Thread {
      override def run() {
        if (openFileSystems != null) {
          openFileSystems foreach (fs => if (fs.isOpen) {fs.close()})
        }
      }
    })
  }

  /** Returns the canonical absolute path from a string.
    * Example inputs: "/usr/local/Viper/backends", "./backends" */
  def canonize(someFileName: String): File = {
    val f = new File(someFileName)
    if (f.isAbsolute) {
      f
    } else {
      java.nio.file.Paths.get(System.getProperty("user.dir"), someFileName).toFile
    }
  }

  /** Check that the file `file` is in (or equal to) the directory `dir`.
    * Requires that `dir` is well-defined, but `file` can be anything. */
  def isInSubDirectory(dir: File, file: File): Boolean = {

    require(dir != null)
    require(dir.isDirectory)

    (file != null) && (file.equals(dir) || isInSubDirectory(dir, file.getParentFile))
  }
}
