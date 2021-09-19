class Idris2Lsp < Formula
  desc "Language server for Idris 2"
  homepage "https://www.idris-lang.org/"
  url "https://github.com/idris-community/idris2-lsp/archive/refs/heads/idris2-0.4.0.zip"
  version "0.0.0-idris2-0.4.0"
  sha256 "fb89a38ecf494030ac0ba7c79806d326c3de57f40cdbf9fed418383f4cd41ab2"
  license "BSD-3-Clause"
  head "https://github.com/idris-community/idris2-lsp.git"

  bottle do
    sha256 cellar: :any,                 big_sur:      "3beffca58897ca836c87544b2a4a1096e70cb0e74e50a1a8b43f6aa4c3a41b75"
    sha256 cellar: :any,                 catalina:     "ad0955e64d0e51cb847765addaf6d850167a9a0edb25323a6446797a55ba4a4a"
    sha256 cellar: :any,                 mojave:       "13c5484d58c87098bb63ee6f861eae120d55b41b43764fae0a07c383658aaf96"
    sha256 cellar: :any_skip_relocation, x86_64_linux: "1eed0bfe631249c078c0ecee22e086d71a07d2b6c12b359e17ae47556a3e0386"
  end

  depends_on "idris2"

  def install
    system "make", "install", "PREFIX=${libexec}"
    bin.install_symlink libexec/"bin/idris2-lsp"
  end

  test do
  end
end
