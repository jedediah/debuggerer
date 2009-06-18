module Debuggerer
  module HashExt
    # Merge only the elements of +hsh+ that are not in +self+
    def augment hsh
      merge(hsh) {|k,v1,v2| v1 }
    end

    def augment! hsh
      merge!(hsh) {|k,v1,v2| v1 }
    end

    # Return a new hash containing only the elements of +self+
    # having a key included in the arguments.
    def filter *a
      a.reduce({}) {|h,k| h[k] = self[k] if key? k; h }
    end

    def filter! *a
      replace filter a
    end

    Hash.send :include, self
  end

  module Helpers
    def extract_options args
      opts = if args[-1].respond_to? :to_hash
               args.pop
             else
               {}
             end
      flags = args.reverse.take_while {|x| x.is_a? Symbol }
      flags.each {|x| opts[x] = true }
      args.replace args[0 .. (-1-flags.size)]
      opts
    end
  end

  class Breakpoint
    include Helpers

    def resolve_coarse x
      case x
      when Module
        {:class => x}
      when String,Regexp
        {:file => x}
      end
    end

    def resolve_fine x
      case x
      when Symbol
        {:method => x}
      when Integer
        {:line => x} if x > 0
      end
    end
      
    def resolve_at x
      a,b = x
      if b.nil?
        resolve_coarse(a) || resolve_fine(a) || {}
      else
        (resolve_coarse(a) ||
         (!a.nil? && {:object => a}) ||
         {}).merge (resolve_fine(b) || {})
      end
    end

    def initialize *args
      @opts = extract_options args
      @opts.augment! resolve_at @opts[:at] if @opts.key? :at
      @opts.augment! :previous => resolve_at(@opts[:ret]) if @opts.key? :ret

      if @opts.key? :raise
        @opts.augment! :event => 'raise'
      elsif @opts.key? :call
        @opts.augment! resolve_at @opts[:call]
        @opts.augment! :event => /(c-)call/
      elsif @opts.key? :ret
        @opts[:previous] ||= {}
        @opts[:previous].augment! resolve_at @opts[:ret]
        @opts[:previous].augment! :event => /(c-)return/
      end

      @opts[:method] = @opts[:method].name if
        [Method,UnboundMethod].include? @opts[:method].class
    end

    def once?
      !!@opts[:once]
    end

    def trigger? ctx
      context_match(ctx, @opts) &&
      context_match(ctx[:previous], @opts[:previous])
    end

    def context_match ctx, opts
      #puts [ctx,opts].inspect
      return false unless !ctx.nil? #and
      return true if opts.nil? #or
      return false unless (opts[:event].nil? || opts[:event] === ctx[:event]) #and
      return false unless (opts[:method].nil? || opts[:method] === ctx[:ident]) #and
      return false unless (opts[:object].nil? || ctx[:binding].eval('self') == opts[:object]) #and
      return false unless (opts[:class].nil? || ctx[:class] == opts[:class]) #and
      return false unless (opts[:file].nil? || opts[:file] === ctx[:file]) #and
      return false unless (opts[:line].nil? || ctx[:line] == opts[:line]) #and
      return false unless (opts[:if].nil? || (ctx[:binding].eval opts[:if] rescue nil))
    end

    def to_s
      @opts.select {|k,v|
        [:class,:object,:method,:file,:line,:if,:event].include? k
      }.map {|k,v|
        "#{k}=#{v}"
      }.join ' '
    end

  end # class Breakpoint

  class Debugger
    include Helpers

    def errmsg msg="Generic error"
      STDERR.puts "\e[31;1m#{msg}\e[0m"
    end

    def initialize &block
      @conf = {}
      @conf[:width] = (ENV['COLUMNS']||78).to_i
      @breakpoints = []
      @stack = []
      @running = false
      @finished = true
      debug &block if block
    end

    @trace_functions ||= []
    @tracing ||= false

    class << self
      attr_reader :trace_functions

      def add_trace_func func
        @trace_functions << func
        set_trace_func method(:meta_trace_function).to_proc unless @tracing
        @tracing = true
      end

      def remove_trace_func func
        tf = @trace_functions.delete func
        if @trace_functions.empty? && @tracing
          set_trace_func nil
          @tracing = false
        end
        tf
      end

      def clear_trace_funcs
        set_trace_func nil
        @trace_functions.clear
        @tracing = false
      end

      def meta_trace_function *a
        @trace_functions.each {|tf| tf[*a] }
      end
    end

    def trace_function *a
      @context[:previous] = nil if @context
      @context = { :previous => @context,
                   :event => a[0],
                   :file => a[1],
                   :line => a[2],
                   :ident => a[3],
                   :binding => a[4],
                   :class => a[5] }

      if @stack.empty? || (@context[:previous] && @context[:previous][:event] =~ /^(c-)call$/)
        @stack.push @context
      else
        @stack.pop if !@stack.empty? && (@context[:previous] && @context[:previous][:event] =~ /^(c-)return$/)
        # note @stack might be empty here.. superfluous returns happen.. I don't know why
        @stack[@stack.size] = @context
      end

      @running = true

      #puts a.inspect; return

      @breakpoints.each {|bp|
        if bp.trigger? @context
          @current_bp = bp
          @breakpoints.delete bp if bp.once?
          STDERR.print "\n\e[1;37;41m Breakpoint: #{bp} \e[0m\n"
          self.class.remove_trace_func @trace_function unless Fiber.yield @context
        end
      }
    end

    def debug &block
      raise ArgumentError.new "block required" unless block
      if !finished?
        errmsg "Debugger already running"
      else
        @finished = false
        @fiber = Fiber.new {
          @trace_function = method(:trace_function).to_proc
          begin
            self.class.add_trace_func @trace_function
            block[]
          ensure
            self.class.remove_trace_func @trace_function
            cleanup
          end
        }
      end
      self
    end # def debug

    attr_reader :context
    def backtrace; @stack; end

    def run dbg=true, &block
      if block
        unless finished?
          errmsg "Debugger already running"
          return
        end
        debug &block
      elsif finished?
        errmsg "Debugger not running and no block given"
        return
      end

      unless finished?
        begin
          @fiber.resume dbg
        rescue FiberError
          cleanup
          errmsg "Debugger stopped abnormally"
        end
        self
      end
    end

    def cleanup
      @running = false
      @finished = true
      @context = nil
      @stack.clear
    end

    def running?
      !!@running
    end

    def finished?
      !!@finished
    end

    def assert_running
      running? or errmsg "Debugger not running" or nil
    end

    def assert_not_finished
      !finished? or errmsg "Debugger not running" or nil
    end

    def finish
      run false if assert_not_finished
    end

    def eval expr
      @context[:binding].eval(expr) if assert_running
    end

    def bp *args
      args.push :file => @context[:file], :line => @context[:line] if
        args.empty? && running?
      @breakpoints << Breakpoint.new(*args)
      self
    end

    def bpif pred, *args
      opts = extract_options args
      bp opts.augment :if => pred
    end

    def bpat a=nil, b=nil, *args
      opts = extract_options args
      bp opts.augment :at => [a,b]
    end

    def bpret a=nil, b=nil, *args
      opts = extract_options args
      bp opts.augment :ret => [a,b]
    end

    def bpex *args
      opts = extract_options args
      bp opts.augment :raise => true
    end

    def clearbp i=nil
      if i
        @breakpoints.delete_at i
      else
        @breakpoints.clear
      end
      self
    end

    def rmbp x
      if x.is_a? Integer
        @breakpoints.delete_at x
      elsif x.is_a? Breakpoint
        @breakpoints.delete x
      end
      self
    end

    def lsbp
      @breakpoints.each_with_index do |bp,i|
        puts "#{i.to_s.ljust 2}   #{bp}" + (bp.once? ? ' (once)' : '')
      end
      self
    end

    EVENT_MNEMONICS = { 'line' => '-',
                        'call' => '>',
                        'return' => '<',
                        'c-call' => '}',
                        'c-return' => '{',
                        'raise' => '!' }

    def format_context ctx
      #inspect_width = @conf[:width] - 49
      inspect_width = @conf[:width] - 25
      inspect_width = 0 if inspect_width < 0
      # "\e[36;1m%4s \e[33;1m%-16.16s \e[37;1m%s \e[35;1m%-24.24s \e[32;1m%.#{inspect_width}s\e[0m" % [
      "\e[36;1m%4s \e[33;1m%-16.16s \e[37;1m%s \e[35;1m%.#{inspect_width}s\e[0m" % [
        ctx[:line].to_s,
        File.basename(ctx[:file]),
        EVENT_MNEMONICS[ctx[:event]],
        "#{ctx[:class]}##{ctx[:ident]}"
        # ctx[:binding].eval('self.inspect')
      ]
    end

    def pos
      STDERR.puts format_context @context if assert_running
      self
    end

    def inspect
      if running?
        format_context @context
      else
        super
      end
    end

    def color_inspect
      if running?
        format_context @context
      else
        super
      end
    end

    def stack
      @stack.each {|ctx| STDERR.puts format_context ctx } if assert_running
      self
    end

    def step &block
      bp :once
      run &block
    end

    def ret a=nil, b=nil, &block
      bpret a, b, :once
      run &block
    end

    define_method :until do |pred, &block|
      bpif pred, :once
      run &block
    end

    define_method :while do |pred, &block|
      bpif "!(#{pred})", :once
      run &block
    end

    def to a=nil, b=nil, &block
      bpat a, b, :once
      run &block
    end

    def ex &block
      bpex :once
      run &block
    end

  end # class Debuggerer

  SOURCE_CACHE = {}

  class Tracer
    DEFAULTS = {
      # [ field, width, color [, options] ]
      #
      # field:     name of field or :space for an empty gap
      #            spaces are collapsed and trimmed from edges
      # width:     Integer => fixed width
      #            Float   => share of space remaining after fixed
      # color:     ansi color string
      # options:   :spill => put on a separate line rather than truncate
      :colors => {
        :file => '33;1',
        :line => '36;1',
        :source => '37;1',
        :watch => '32;1'
      },
      :source => true
    }

    def initialize opts={}, &block
      @conf = DEFAULTS.merge opts
      @condition = @conf[:condition]
      @watch = @conf[:watch]
      @changes = !!@conf[:changes]
      @source = !!@conf[:source]
      @width = @conf[:width] || (ENV["COLUMNS"] || 78).to_i

      @last_file = @watch_seen = @watch_last_value = nil
      @state = :pre

      begin
        set_trace_func method(:trace_function).to_proc
        @state = :almost
        @return_value = yield
      ensure
        set_trace_func nil
      end
    end

    attr_reader :return_value

    define_method :trace_function do |event, file, line, ident, bind, klass|
      if @conf[:raw]
        puts [event,file,line,ident,bind,klass].inspect
        return
      end

      case @state
      when :pre
        return
      when :almost
        unless klass == Tracer && ident == :initialize
          @state = :in
          redo # <3 redo
        end
      when :in
        if klass == Tracer && ident == :initialize && bind.eval('self') == self
          @state = :out
        elsif event == 'line' && (!@condition || (bind.eval(@condition) rescue nil))
          # puts [event,file,line,ident,bind,klass].inspect

          watch_show = if @watch
                         begin
                           watch_value = bind.eval @watch
                           watch_defined = true
                           watch_changed = !@watch_seen || watch_value != @watch_last_value
                           @watch_seen = true
                           @watch_last_value = watch_value
                           !@changes || watch_changed
                         rescue
                           watch_defined = watch_changed = false
                         end
                       end

          if !@watch || watch_show
            STDERR.puts(
              format_trace_line :event => event,
                                :file => file,
                                :line => line,
                                :ident => ident,
                                :class => klass,
                                :watch => watch_show && watch_value,
                                :new_file => @last_file != file )
            @last_file = file
          end

        end # if klass == Tracer ...
      end # case @state
    end # def trace_function

    def format_trace_line params
      # puts @conf.inspect
      params = @conf.merge params

      line = params[:line]
      file = params[:file]
      width = params[:width] || 78
      watch = params[:watch]
      watch = watch.inspect if watch

      line_s = line.to_s.ljust(5)

      src_s = nil
      if params[:source]
        src_s = if file == "(irb)"
                   IRB.CurrentContext.io.line(line).chomp
                 elsif src_lines = SOURCE_CACHE[file]
                   src_lines[line-1]
                 elsif File.exist? file
                   (SOURCE_CACHE[file] = File.readlines(file).map(&:rstrip))[line-1]
                 end
      end

      src_s ||= "#{params[:event]} #{params[:class]}:#{params[:ident]}"
      src_width = @width - line_s.size

      format = if watch
                 if src_width-watch.size-1 > 10
                   :oneline
                 else
                   :multiline
                 end
               else
                 :nowatch
               end

      src_width -= watch.size+1 if format == :oneline

      if src_s.size > src_width
        # if the line is too long, truncate it and append a red indicator
        src_s = src_s[0,src_width-1] + "\e[31;1m>"
      elsif format == :oneline
        # pad src_line to push the watch to the right edge
        src_s = src_s.ljust src_width
      end

      output = ''
      output << "\e[#{params[:colors][:file]}mIn #{file}:\n" if params[:new_file]
      output << "\e[#{params[:colors][:line]}m#{line_s}\e[#{params[:colors][:source]}m#{src_s}"
      output << "\n" if format == :multiline
      output << "\e[#{params[:colors][:watch]}m#{watch}\e[0m" if format != :nowatch
      return output
    end # def format_trace_line

  end # class Tracer

  class << self

    def debug &block
      Debugger.new &block
    end

    [:to,:while,:until,:ex].each do |meth|
      define_method meth do |*a, &block|
        dbg = Debugger.new &block
        dbg.send meth, *a
        dbg
      end
    end

    def trace opts={}, &block
      tr = Tracer.new opts, &block
      tr.return_value
    end

    def trace_if pred, opts={}, &block
      trace opts.merge(:condition => pred), &block
    end

    def watch watch, opts={}, &block
      trace opts.merge(:watch => watch), &block
    end

    def watch_if watch, pred, opts={}, &block
      trace opts.merge(:watch => watch, :condition => pred), &block
    end

    def watch_changes watch, opts={}, &block
      trace opts.merge(:watch => watch, :changes => true), &block
    end

    def install
    end
  end # class << self

  module ToplevelCommands
    def run_to *a, &block
      Debuggerer.to *a, &block
    end

    def run_while *a, &block
      Debuggerer.while *a, &block
    end

    def run_until *a, &block
      Debuggerer.while *a, &block
    end

    def run_ex *a, &block
      Debuggerer.ex *a, &block
    end
  end

  module ModuleCommands
    def run_to *a, &block
      Debuggerer.to self, *a, &block
    end
  end
end # module Debuggerer

