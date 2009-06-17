require "rake"
require "rake/rdoctask"
require "rake/gempackagetask"

gemspec = eval File.read(File.join(File.expand_path(File.dirname(__FILE__)),"debuggerer.gemspec"))

Rake::GemPackageTask.new gemspec do |pkg|
  pkg.gem_spec = gemspec
end
