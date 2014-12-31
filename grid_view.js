/**
 * Manages the grid of cells.
 *
 * Creates an grid of cells, and updates the state of the grid according
 * to a string describing the state of each cell.
 *
 * @param {Element} element The DOM element that contains the view.
 * @param {Object} options Dictionary with the following keys:
 *    rows: The number of rows in the grid
 *    cols: The number of columns in the grid
 *    tileset.cols: The number of columns in the tileset
 *    tileset.filename: The file name of the tileset
 *    tileset.tile_width: The width of a tile
 *    tileset.tile_height: The height of a tile
 */
var GridView = function(element, options) {
	this.element_ = element;
	this.element_.width = options.cols * options.tileset.tile_width;
	this.element_.height = options.rows * options.tileset.tile_height;

	this.tileset_image_ = new Image();
	this.tileset_image_.src = options.tileset.filename;
	var that = this;
	this.tileset_image_loaded_ = false;
	this.tileset_image_.onload = function() {
		that.tileset_image_loaded_ = true;
	};

	this.context_ = element.getContext('2d');

	this.rows_ = options.rows;
	this.cols_ = options.cols;
	this.tilset_cols_ = options.tileset.cols;
	this.tile_width_ = options.tileset.tile_width;
	this.tile_height_ = options.tileset.tile_height;
};

/**
 * Update the view.
 * @param {string} str A string containing the state of
 *   each cell, in row major order.
 */
GridView.prototype.show = function(str) {
	if (str.length != this.rows_ * this.cols_) {
		console.error('str had different length to the number of cells');
		return;
	}
	// If image hasn't loaded, call this function again when it has.
	if (!this.tileset_image_loaded_) {
		var that = this;
		this.tileset_image_.onload = function() {
			that.show(str);
			that.tileset_image_loaded_ = true;
		};
	}

	var w = this.tile_width_;
	var h = this.tile_height_;

	for (var r = 0; r < this.rows_; r++) {
		for (var c = 0; c < this.cols_; c++) {
			var i = r * this.cols_ + c;
			var tile_idx = str.charCodeAt(i);
			var tr = Math.floor(tile_idx / this.tilset_cols_); // Bitwise OR operation
			var tc = tile_idx % this.tilset_cols_;
			this.context_.drawImage(this.tileset_image_, tc * w, tr * h, w, h, c * w, r * h, w, h);
		}
	}
};