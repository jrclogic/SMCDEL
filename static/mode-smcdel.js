window.define = window.define || ace.define;

define('ace/mode/smcdel', function(require, exports, module) {
    var oop = require("ace/lib/oop");
    var TextMode = require("ace/mode/text").Mode;
    var SmcdelHighlightRules = require("ace/mode/smcdel_highlight_rules").SmcdelHighlightRules;
    var Mode = function() {
        this.HighlightRules = SmcdelHighlightRules;
    };
    oop.inherits(Mode, TextMode);
    (function() {
        // Extra logic goes here, so far we have nothing.
    }).call(Mode.prototype);
    exports.Mode = Mode;
});

define('ace/mode/smcdel_highlight_rules', function(require, exports, module) {
    var oop = require("ace/lib/oop");
    var TextHighlightRules = require("ace/mode/text_highlight_rules").TextHighlightRules;
    var SmcdelHighlightRules =  function() {
        var keywords = "VARS|LAW|OBS|VALID|WHERE|TRUE"; // TODO: how to include "?"
        var builtinConstants = "AND|OR|ONEOF|Top|knows|that|whether|comknow|";
        var builtinFunctions = ""; // unused
        var keywordMapper = this.createKeywordMapper({
            "support.function": builtinFunctions,
            "keyword": keywords,
            "constant.language": builtinConstants
        }, "identifier", true);
        this.$rules = {
            "start" : [ {
                token : "comment",
                regex : "--*.*$"
            }, {
                token : "constant.numeric", // float
                regex : "[+-]?\\d+(?:(?:\\.\\d*)?(?:[eE][+-]?\\d+)?)?\\b"
            }, {
                token : keywordMapper,
                regex : "[a-zA-Z_$][a-zA-Z0-9_$]*\\b"
            }, {
                token : "text",
                regex : "\\s+"
            } ]
        };
    };
    oop.inherits(SmcdelHighlightRules, TextHighlightRules);
    exports.SmcdelHighlightRules = SmcdelHighlightRules;
});
