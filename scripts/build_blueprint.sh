#!/usr/bin/env bash
set -e

# Build blueprint and apply SleepLoop theme
# Run from repo root: bash scripts/build_blueprint.sh

echo "Building blueprint..."
leanblueprint web 2>&1

WEB="blueprint/src/web"

# Copy custom theme (lives in blueprint/src/styles/, survives rebuilds)
cp blueprint/src/styles/theme-sleepy.css "$WEB/styles/"

# Inject theme stylesheet after theme-white.css
sed -i 's|theme-white.css" />|theme-white.css" /><link rel="stylesheet" href="styles/theme-sleepy.css" />|g' "$WEB"/*.html

# Lowercase title, remove "– Formalization Blueprint"
sed -i 's/A Math Loop That Sleeps and Dreams – Formalization Blueprint/a math loop that sleeps and dreams/g' "$WEB"/*.html

# Remove empty bibliography page
rm -f "$WEB/sect0002.html"
sed -i '/Bibliography/d' "$WEB"/*.html

# Add title to index page (plasTeX omits it on the root page)
sed -i 's|<svg  id="toc-toggle" class="icon icon-list-numbered "><use xlink:href="symbol-defs.svg#icon-list-numbered"></use></svg>|<svg  id="toc-toggle" class="icon icon-list-numbered "><use xlink:href="symbol-defs.svg#icon-list-numbered"></use></svg>\n<h1 id="doc_title"><a href="index.html">a math loop that sleeps and dreams</a></h1>|' "$WEB/index.html"

# Copy to docs/ for GitHub Pages
rm -rf docs
cp -r "$WEB" docs

echo "Done. Preview: open docs/index.html"
