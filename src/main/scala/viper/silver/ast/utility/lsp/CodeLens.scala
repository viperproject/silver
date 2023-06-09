package viper.silver.ast.utility.lsp

trait HasCodeLens {
  def getCodeLens: Seq[CodeLens]
}

case class CodeLens(
    /** The range in which this code lens is valid. Should only span a single line. */
    range: RangePosition,
    /** The command this code lens represents. */
    command: String,
) extends HasRangePositions with BelongsToFile {
  override def rangePositions: Seq[RangePosition] = Seq(range)
  override def file = range.file
}
