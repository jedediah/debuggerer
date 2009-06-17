module Debuggerer
  class Breakpoint
    def initialize opts
      @once = opts[:once]
    end

    def once?
      !!@once
    end

    def trigger? params
      true
    end

    def to_s
      "unconditional"
    end
  end

  class FileLineBreakpoint < Breakpoint
    def initialize opts
      super
      @file = opts[:file]
      @file = File.expand_path @file if @file.respond_to? :to_str
      @line = opts[:line].to_i
    end

    def trigger? params
      params[:line] == @line &&
      params[:event] == 'line' &&
      @file === params[:file]
    end

    def to_s
      "line #{@line} of #{@file}"
    end
  end

  class MethodCallBreakpoint < Breakpoint
    def initialize opts
      super
      @class = opts[:class]
      @class = @class.class unless @class.is_a? Module
      @method = opts[:method].to_s.intern
    end

    def trigger? params
      params[:ident] == @method &&
      params[:event] =~ /^(c-)?call$/ &&
      params[:class] == @class
    end

    def to_s
      "call to #{@class}##{@method}"
    end
  end

  class ExceptionBreakpoint < Breakpoint
    def trigger? params
      params[:event] == 'raise'
    end

    def to_s
      "all exceptions"
    end
  end

  class ConditionalBreakpoint < Breakpoint
    def initialize opts
      super
      @pred = opts[:pred].to_s
    end

    def trigger? params
      params[:binding].eval @pred rescue nil
    end

    def to_s
      "if #{@pred}"
    end
  end

  class Debugger

    def errmsg msg="Generic error"
      STDERR.puts "\e[31;1m#{msg}\e[0m"
    end

    def initialize &block
      @breakpoints = []
      debug &block if block
    end

    def debug &block
      raise ArgumentError.new "block required" unless block
      if running?
        errmsg "Debugger already running"
      else
        @fiber = Fiber.new {
          begin
            set_trace_func proc { |*a|
              @context = { :event => a[0],
                           :file => a[1],
                           :line => a[2],
                           :ident => a[3],
                           :binding => a[4],
                           :class => a[5] }

              @breakpoints.each {|bp|
                if bp.trigger? @context
                  @current_bp = bp
                  @breakpoints.delete bp if bp.once?
                  STDERR.print "\n\e[1;37;41m Breakpoint #{bp} \e[0m\n"
                  set_trace_func nil unless Fiber.yield @context
                end
              }
            }
            block[]
          ensure
            set_trace_func nil
            @running = false
          end
        }
        @running = true
      end
    end # def debug

    attr_reader :context

    def run dbg=true, &block
      self.debug &block if block

      if running?
        begin
          @fiber.resume dbg
        rescue FiberError
          @running = false
          errmsg "Debugger stopped abnormally"
        end
      else
        errmsg "Debugger not running and no block given"
      end
    end

    def running?
      @running
    end

    def finish
      run false
    end

    def eval expr
      errmsg "Debugger not running" unless running?
      @context && @context[:binding].eval(expr)
    end

    def break once=false
      @breakpoints << Breakpoint.new(:once => once)
    end

    def break_if pred, once=false
      @breakpoints << ConditionalBreakpoint.new(:pred => pred, :once => once)
    end

    def break_at a, b, once=false
      if a.is_a?(Regexp) || a.is_a?(String)
        @breakpoints << FileLineBreakpoint.new(:file => a, :line => b, :once => once)
      else
        @breakpoints << MethodCallBreakpoint.new(:class => a, :method => b, :once => once)
      end
    end

    def break_ex once=false
      @breakpoints << ExceptionBreakpoint.new(:once => once)
    end

    def clearbp i=nil
      if i
        @breakpoints.delete_at i
      else
        @breakpoints.clear
      end
    end

    def rmbp x
      if x.is_a? Integer
        @breakpoints.delete_at x
      elsif x.is_a? Breakpoint
        @breakpoints.delete x
      end        
    end

    def lsbp
      @breakpoints.each_with_index do |bp,i|
        puts "#{i.to_s.ljust 2}   #{bp}" + (bp.once? ? ' (once)' : '')
      end
    end

    def step &block
      self.break true
      run &block
    end

    def run_until pred, &block
      break_if pred, true
      run &block
    end

    def run_to a, b, &block
      break_at a, b, true
      run &block
    end

    def run_ex &block
      break_ex true
      run &block
    end

  end # class Debugger

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

=begin
      fields = @conf[:trace_fields].dup
      fields.delete {|x| x[0] == :watch } unless @conf[:watch]
      fixed,flexi = fields.reduce([]) {|a,x|
        if x[0] != :space || a.last && a.last[0] != :space && x != fields.last
          a << x
        elsif a.last && a.last[0] == :space
          a[-1] = x if a.last[1] < x[1]
        end
      }.partition {|x| x[1].is_a? Integer }

      spill = []
      while !fixed.empty? @width < (fixed_sum = fixed.sum {|x| x[1] })
        spill << fixed.delete fixed.max_by {|x| x[1] }
      end
=end      

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
      #puts [event,file,line,ident,bind,klass].inspect
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
      Debugger.new block
    end

    def run_until pred, &block
      dbg = Debugger.new &block
      dbg.run_until pred
      dbg
    end

    def run_to a, b, &block
      dbg = Debugger.new &block
      dbg.run_to a, b
      dbg
    end

    def run_ex &block
      dbg = Debugger.new &block
      dbg.run_ex
      dbg
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

  end # class << self
end # module Debuggerer
