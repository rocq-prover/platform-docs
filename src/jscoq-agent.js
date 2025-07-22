///@ts-check
// Source: https://github.com/jscoq/coqdoc-template
/**
 * Injects jsCoq into an existing page.
 * This script is adapted from the Software Foundations jsCoq build.
 * So, it may require some tweaking depending on your development and styles.
 */
import { JsCoq, Deprettify } from './node_modules/jscoq/dist/frontend/index.js';

function jsCoqInject() {
    var b = document.body;
    b.setAttribute('id', 'ide-wrapper');
    b.classList.add('toggled');
    b.classList.add(isTerse() ? 'terse' : 'full');

    var plug = document.createElement('div');
    plug.setAttribute('id', 'jscoq-plug');
    plug.addEventListener('click', jsCoqStart);
    b.append(plug);
}

var jsCoqShow = location.search === '?jscoq=on' ||
                location.search !== '?jscoq=off' && localStorage.jsCoqShow === 'true';

var jscoq_ids  = ['#main > div.code, #main > div.HIDEFROMHTML > div.code'];

var sp = new URLSearchParams(location.search);

// Dynamically compute base_path for jsCoq
function computeBasePath() {
    var scriptElem = document.currentScript;
    var scriptUrl = '';
    if (scriptElem && scriptElem instanceof HTMLScriptElement && scriptElem.src) {
        scriptUrl = scriptElem.src;
    }
    // Parse paths into segments
    var scriptPath = scriptUrl ? new URL(scriptUrl).pathname : '';
    var scriptSegments = scriptPath.split('/').filter(Boolean);

    var htmlPath = window.location.pathname;
    var htmlSegments = htmlPath.split('/').filter(Boolean);

    // Remove file names, keep directories
    var jsDirSegments = scriptSegments.slice(0, -1);
    var htmlDirSegments = htmlSegments.slice(0, -1);

    // Find common prefix length
    var i = 0;
    while (i < jsDirSegments.length && i < htmlDirSegments.length && jsDirSegments[i] === htmlDirSegments[i]) {
        i++;
    }

    // Build relative path: up from HTML dir to common ancestor, then down to JS dir
    var upLevels = htmlDirSegments.length - i;
    var relPath = '';
    if (upLevels > 0) {
        relPath = '../'.repeat(upLevels);
    }
    var downPath = jsDirSegments.slice(i).join('/');
    if (downPath) {
        if (relPath && !relPath.endsWith('/')) relPath += '/';
        relPath += downPath;
    }
    // If still empty, use current directory
    if (relPath === '') {
        relPath = './';
    }
    return relPath;
}

var jscoq_opts = {
    backend:   sp.get('backend') || 'wa',
    layout:    'flex',
    show:      jsCoqShow,
    focus:     false,
    replace:   true,
    // EJGA I disable company Coq as it a bit confusing for teaching
    // editor:    { mode: { 'company-coq': true }, className: 'jscoq code-tight' },
    editor:    { className: 'jscoq code-tight' },
    init_pkgs: ['init'],
    all_pkgs:  { '+': ['coq', 'equations'] },
    init_import: ['utf8'],
    implicit_libs: true,
    node_modules_path: computeBasePath() + '/node_modules/',
};

async function jsCoqLoad() {
    // - remove empty code fragments (coqdoc generates some spurious ones)
    for (let code of document.querySelectorAll('#main > div.code')) {
        if (code.textContent?.match(/^\s*$/)) code.remove();
    }

    // - make page div focusable so that keyboard scrolling works
    var page = /** @type {HTMLElement} */ (document.querySelector('#page'));
    page.setAttribute('tabindex', '-1');
    page.focus();

    // - load and start jsCoq, not needed in 8.17
    // await JsCoq.load(jscoq_opts.base_path);

    Deprettify.REPLACES.push(   // LF,PLF define their own versions (for Imp)
        [/∨/g, '\\/'], [/∧/g, '/\\'], [/↔/g, '<->'], [/≤/g, '<='], [/≠/g, '<>'],
        [/∈/g, '\\in']);

    var coq = await JsCoq.start(jscoq_ids, jscoq_opts);
    //@ts-ignore
    window.coq = coq;
    window.addEventListener('beforeunload', () => { localStorage.jsCoqShow = coq.layout.isVisible(); })
}

function jsCoqStart() {
    //@ts-ignore
    window.coq.layout.show();
}

/** SF-style terse mode */
function isTerse() {
    return !!document.querySelector('[src$="/slides.js"]');
}

if (location.search !== '?jscoq=no') {
    window.addEventListener('DOMContentLoaded', () => {
        jsCoqInject();
        jsCoqLoad();
    });
}
