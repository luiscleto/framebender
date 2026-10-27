import Base
import ../protocol.bend as P

# P.Fasta.plain on the cases checked against samtools faidx 1.24 (each: did
# samtools index it and serve it as B.Fasta.parse reads it?). Checked by
# evaluation: bend test/plain_cases.bend --check-only

def pre() -> {P.Fasta.plain("NOTE\n>c\nACGT\n") == False{} : Bool}:
  {==}
def emptyline() -> {P.Fasta.plain(">c\nACGT\n\nTT\n") == False{} : Bool}:
  {==}
def uneven() -> {P.Fasta.plain(">c\nAC\nACGT\n") == False{} : Bool}:
  {==}
def shortlast() -> {P.Fasta.plain(">c\nACGT\nAC\n") == True{} : Bool}:
  {==}
def dup() -> {P.Fasta.plain(">c\nACGT\n>c\nGG\n") == True{} : Bool}:
  {==}
def dupbad() -> {P.Fasta.plain(">c\nACGT\n>c\nG\nGG\n") == False{} : Bool}:
  {==}
def noname() -> {P.Fasta.plain(">\nACGT\n>c\nAA\n") == True{} : Bool}:
  {==}
def ctrl() -> {P.Fasta.plain(">c\nAC\u{1}GT\n") == False{} : Bool}:
  {==}
def vt() -> {P.Fasta.plain(">c\u{b}x\nACGT\n") == False{} : Bool}:
  {==}
def trailingempty() -> {P.Fasta.plain(">c\nACGT\n\n>d\nAA\n") == True{} : Bool}:
  {==}
def crlf() -> {P.Fasta.plain(">c\r\nACGT\r\nAC\r\n") == True{} : Bool}:
  {==}
def crmix() -> {P.Fasta.plain(">c\nACGT\r\nAC\n") == False{} : Bool}:
  {==}
def empty_kept() -> {P.Fasta.plain(">e\n>c\nACGT\n") == False{} : Bool}:
  {==}
def midcr() -> {P.Fasta.plain(">c\nAC\rGT\n") == False{} : Bool}:
  {==}
def space() -> {P.Fasta.plain(">c\nAC GT\n") == False{} : Bool}:
  {==}
def noeol() -> {P.Fasta.plain(">c\nACGT") == True{} : Bool}:
  {==}
def emptyfile() -> {P.Fasta.plain("") == False{} : Bool}:
  {==}
def leadsp() -> {P.Fasta.plain("> c\nACGT\n") == False{} : Bool}:
  {==}
def nul() -> {P.Fasta.plain(">a\u{0}b\nACGT\n") == False{} : Bool}:
  {==}
def lastempty() -> {P.Fasta.plain(">c\nACGT\n>d\n") == False{} : Bool}:
  {==}
def midnoname() -> {P.Fasta.plain(">c\nACGT\n>\n>d\nTT\n") == True{} : Bool}:
  {==}
def newline_only() -> {P.Fasta.plain("\n") == False{} : Bool}:
  {==}
# samtools 1.24 indexes it (c 4 4 4 5): blank lines before the first header.
def leadblank() -> {P.Fasta.plain("\n>c\nACGT\n") == True{} : Bool}:
  {==}
