class Idris2Lsp < Formula
  desc "Language server for Idris 2"
  homepage "https://www.idris-lang.org/"
  url "https://github.com/idris-community/idris2-lsp/archive/refs/heads/idris2-0.5.1.zip"
  version "0.0.0-idris2-0.5.1"
  sha256 "f2fa76f1a916c9df8e0e6a1e7ad96738861f21662c91f0209d20ab2c5ba6d889"
  license "BSD-3-Clause"
  head "https://github.com/idris-community/idris2-lsp.git"

  depends_on "idris2"

  def install
    system "make", "install", "PREFIX=#{libexec}"
    bin.install_symlink libexec/"bin/idris2-lsp"
  end

  test do
  end
end
