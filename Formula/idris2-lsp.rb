class Idris2Lsp < Formula
  desc "Language server for Idris 2"
  homepage "https://www.idris-lang.org/"
  url "https://github.com/idris-community/idris2-lsp/archive/refs/heads/idris2-0.5.1.zip"
  version "0.0.0-idris2-0.5.1"
  sha256 "f2fa76f1a916c9df8e0e6a1e7ad96738861f21662c91f0209d20ab2c5ba6d889"
  license "BSD-3-Clause"
  head "https://github.com/idris-community/idris2-lsp.git", :branch => "main"

  depends_on "idris2"

  def install
    system Formula["idris2"].bin/"idris2", "--build", "lsp.ipkg"
    system "make", "install-only", "PREFIX=#{prefix}"
  end

  test do
  end
end
