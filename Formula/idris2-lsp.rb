class Idris2Lsp < Formula
  desc "Language server for Idris 2"
  homepage "https://www.idris-lang.org/"
  url "https://github.com/idris-community/idris2-lsp/archive/refs/heads/idris2-0.5.1.zip"
  version "0.0.0-idris2-0.5.1"
  sha256 "fb89a38ecf494030ac0ba7c79806d326c3de57f40cdbf9fed418383f4cd41ab2"
  license "BSD-3-Clause"
  head "https://github.com/idris-community/idris2-lsp.git"

  depends_on "idris2"

  def install
    system "make", "install", "PREFIX=${libexec}"
    bin.install_symlink libexec/"bin/idris2-lsp"
  end

  test do
  end
end
